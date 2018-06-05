/* Malloc implementation for multiple threads without lock contention.
   Copyright (C) 2001-2018 Free Software Foundation, Inc.
   This file is part of the GNU C Library.
   Contributed by Wolfram Gloger <wg@malloc.de>, 2001.

   The GNU C Library is free software; you can redistribute it and/or
   modify it under the terms of the GNU Lesser General Public License as
   published by the Free Software Foundation; either version 2.1 of the
   License, or (at your option) any later version.

   The GNU C Library is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   Lesser General Public License for more details.

   You should have received a copy of the GNU Lesser General Public
   License along with the GNU C Library; see the file COPYING.LIB.  If
   not, see <http://www.gnu.org/licenses/>.  */

#include <stdbool.h>

#if HAVE_TUNABLES
# define TUNABLE_NAMESPACE malloc
#endif
#include <elf/dl-tunables.h>

/* Compile-time constants.  */

#define HEAP_MIN_SIZE (32 * 1024)
#ifndef HEAP_MAX_SIZE
# ifdef DEFAULT_MMAP_THRESHOLD_MAX
#  define HEAP_MAX_SIZE (2 * DEFAULT_MMAP_THRESHOLD_MAX)
# else
#  define HEAP_MAX_SIZE (1024 * 1024) /* must be a power of two */
# endif
#endif

/* HEAP_MIN_SIZE and HEAP_MAX_SIZE limit the size of mmap()ed heaps
   that are dynamically created for multi-threaded programs.  The
   maximum size must be a power of two, for fast determination of
   which heap belongs to a chunk.  It should be much larger than the
   mmap threshold, so that requests with a size just below that
   threshold can be fulfilled without creating too many heaps.  */

/***************************************************************************/

#define top(ar_ptr) ((ar_ptr)->top)

/* A heap is a single contiguous memory region holding (coalesceable)
   malloc_chunks.  It is allocated with mmap() and always starts at an
   address aligned to HEAP_MAX_SIZE.  */
//模拟堆
typedef struct _heap_info
{
  mstate ar_ptr; /* Arena for this heap. */ //指向所属分配区的指针
  struct _heap_info *prev; /* Previous heap. */ //将同一个分配区中的sub_heap连接起来
  size_t size;   /* Current size in bytes. */ //sub_heap的内存大小,可讀可寫區域(被分配了也算)
  size_t mprotect_size; /* Size in bytes that has been mprotected
                           PROT_READ|PROT_WRITE.  */  //被读写保护的内存大小,即可读可写的内存大小(未分配的内存大小)
  /* Make sure the following data is properly aligned, particularly
     that sizeof (heap_info) + 2 * SIZE_SZ is a multiple of
     MALLOC_ALIGNMENT. */
  char pad[-6 * SIZE_SZ & MALLOC_ALIGN_MASK]; // -6 * SIZE_SZ & MALLOC_ALIGN_MASK = 0 ,检验对齐

} heap_info;

/* Get a compile-time error if the heap_info padding is not correct
   to make alignment work as expected in sYSMALLOc.  */
extern int sanity_check_heap_info_alignment[(sizeof (heap_info)
                                             + 2 * SIZE_SZ) % MALLOC_ALIGNMENT
                                            ? -1 : 1];

/* Thread specific data.  */

static __thread mstate thread_arena attribute_tls_model_ie;

/* Arena free list.  free_list_lock synchronizes access to the
   free_list variable below, and the next_free and attached_threads
   members of struct malloc_state objects.  No other locks must be
   acquired after free_list_lock has been acquired.  */

__libc_lock_define_initialized (static, free_list_lock);
static size_t narenas = 1; //全局变量,表示当前分配区的数量
static mstate free_list;//空闲分配区的单项链表

/* list_lock prevents concurrent writes to the next member of struct
   malloc_state objects.

   Read access to the next member is supposed to synchronize with the
   atomic_write_barrier and the write to the next member in
   _int_new_arena.  This suffers from data races; see the FIXME
   comments in _int_new_arena and reused_arena.

   list_lock also prevents concurrent forks.  At the time list_lock is
   acquired, no arena lock must have been acquired, but it is
   permitted to acquire arena locks subsequently, while list_lock is
   acquired.  */
__libc_lock_define_initialized (static, list_lock);

/* Already initialized? */
int __malloc_initialized = -1;  //标志ptmalloc是否初始化

/**************************************************************************/


/* arena_get() acquires an arena and locks the corresponding mutex.
   First, try the one last locked successfully by this thread.  (This
   is the common case and handled with a macro for speed.)  Then, loop
   once over the circularly linked list of arenas.  If no arena is
   readily available, create a new one.  In this latter case, `size'
   is just a hint as to how much memory will be required immediately
   in the new arena. */
/*
 * 获取分配区,调用 arena_lock 尝试对该分配区加锁
 */
#define arena_get(ptr, size) do { \
      ptr = thread_arena;/*线程先查看线程私有实例中是否已经存在一个分配区,尝试对其加锁*/						      \
      arena_lock (ptr, size);						      \
  } while (0)
/*
 * 如果加锁成功,使用该分配区分配内存
 * 如果对该分配区加锁失败,调用 arena_get2 获得一个分配区指针
 */
#define arena_lock(ptr, size) do {					      \
      if (ptr)								      \
        __libc_lock_lock (ptr->mutex);					      \
      else								      \
        ptr = arena_get2 ((size), NULL);				      \
  } while (0)

/* find the heap and corresponding arena for a given ptr */

#define heap_for_ptr(ptr) \
  ((heap_info *) ((unsigned long) (ptr) & ~(HEAP_MAX_SIZE - 1)))
#define arena_for_chunk(ptr) \
  (chunk_main_arena (ptr) ? &main_arena : heap_for_ptr (ptr)->ar_ptr)


/**************************************************************************/

/* atfork support.  */

/* The following three functions are called around fork from a
   multi-threaded process.  We do not use the general fork handler
   mechanism to make sure that our handlers are the last ones being
   called, so that other fork handlers can use the malloc
   subsystem.  */

void
__malloc_fork_lock_parent (void)
{
  if (__malloc_initialized < 1)
    return;

  /* We do not acquire free_list_lock here because we completely
     reconstruct free_list in __malloc_fork_unlock_child.  */

  __libc_lock_lock (list_lock);

  for (mstate ar_ptr = &main_arena;; )
    {
      __libc_lock_lock (ar_ptr->mutex);
      ar_ptr = ar_ptr->next;
      if (ar_ptr == &main_arena)
        break;
    }
}

void
__malloc_fork_unlock_parent (void)
{
  if (__malloc_initialized < 1)
    return;

  for (mstate ar_ptr = &main_arena;; )
    {
      __libc_lock_unlock (ar_ptr->mutex);
      ar_ptr = ar_ptr->next;
      if (ar_ptr == &main_arena)
        break;
    }
  __libc_lock_unlock (list_lock);
}

void
__malloc_fork_unlock_child (void)
{
  if (__malloc_initialized < 1)
    return;

  /* Push all arenas to the free list, except thread_arena, which is
     attached to the current thread.  */
  __libc_lock_init (free_list_lock);
  if (thread_arena != NULL)
    thread_arena->attached_threads = 1;
  free_list = NULL;
  for (mstate ar_ptr = &main_arena;; )
    {
      __libc_lock_init (ar_ptr->mutex);
      if (ar_ptr != thread_arena)
        {
	  /* This arena is no longer attached to any thread.  */
	  ar_ptr->attached_threads = 0;
          ar_ptr->next_free = free_list;
          free_list = ar_ptr;
        }
      ar_ptr = ar_ptr->next;
      if (ar_ptr == &main_arena)
        break;
    }

  __libc_lock_init (list_lock);
}

#if HAVE_TUNABLES
static inline int do_set_mallopt_check (int32_t value);
void
TUNABLE_CALLBACK (set_mallopt_check) (tunable_val_t *valp)
{
  int32_t value = (int32_t) valp->numval;
  if (value != 0)
    __malloc_check_init ();
}

# define TUNABLE_CALLBACK_FNDECL(__name, __type) \
static inline int do_ ## __name (__type value);				      \
void									      \
TUNABLE_CALLBACK (__name) (tunable_val_t *valp)				      \
{									      \
  __type value = (__type) (valp)->numval;				      \
  do_ ## __name (value);						      \
}

TUNABLE_CALLBACK_FNDECL (set_mmap_threshold, size_t)
TUNABLE_CALLBACK_FNDECL (set_mmaps_max, int32_t)
TUNABLE_CALLBACK_FNDECL (set_top_pad, size_t)
TUNABLE_CALLBACK_FNDECL (set_perturb_byte, int32_t)
TUNABLE_CALLBACK_FNDECL (set_trim_threshold, size_t)
TUNABLE_CALLBACK_FNDECL (set_arena_max, size_t)
TUNABLE_CALLBACK_FNDECL (set_arena_test, size_t)
#if USE_TCACHE
TUNABLE_CALLBACK_FNDECL (set_tcache_max, size_t)
TUNABLE_CALLBACK_FNDECL (set_tcache_count, size_t)
TUNABLE_CALLBACK_FNDECL (set_tcache_unsorted_limit, size_t)
#endif
#else
/* Initialization routine. */
#include <string.h>
extern char **_environ;

static char *
next_env_entry (char ***position)
{
  char **current = *position;
  char *result = NULL;

  while (*current != NULL)
    {
      if (__builtin_expect ((*current)[0] == 'M', 0)
          && (*current)[1] == 'A'
          && (*current)[2] == 'L'
          && (*current)[3] == 'L'
          && (*current)[4] == 'O'
          && (*current)[5] == 'C'
          && (*current)[6] == '_')
        {
          result = &(*current)[7];

          /* Save current position for next visit.  */
          *position = ++current;

          break;
        }

      ++current;
    }

  return result;
}
#endif


#ifdef SHARED
static void *
__failing_morecore (ptrdiff_t d)
{
  return (void *) MORECORE_FAILURE;
}

extern struct dl_open_hook *_dl_open_hook;
libc_hidden_proto (_dl_open_hook);
#endif


//ptmalloc 初始化函数
static void
ptmalloc_init (void)
{
  if (__malloc_initialized >= 0)  //>=0表示已经初始化直接返回即可
    return;

  __malloc_initialized = 0;   //改为0表示正在初始化,确保只初始化一次

#ifdef SHARED
  /* In case this libc copy is in a non-default namespace, never use brk.
     Likewise if dlopened from statically linked program.  */
  /*
   * Ptmalloc 需要保证只有主分配区才能使用 sbrk()分配连续虚拟内存空间,如果有多个分
   * 配区使用 sbrk()就不能获得连续的虚拟地址空间,大多数情况下 Glibc 库都是以动态链接库
   * 的形式加载的,处于默认命名空间,多个进程共用 Glibc 库,Glibc 库代码段在内存中只有一
   * 份拷贝,数据段在每个用户进程都有一份拷贝。但如果 Glibc 库不在默认名字空间,或是用
   * 户程序是静态编译的并调用了 dlopen 函数加载 Glibc 库中的 ptamalloc_init()
   * ptmalloc 不允许使用 sbrk()分配内存,只需修改__morecore 函数指针指向__failing_morecore
   * 就可以禁止使用 sbrk()了,__morecore 默认指向 sbrk()
   *
   * */
  Dl_info di;
  struct link_map *l;

  if (_dl_open_hook != NULL
      || (_dl_addr (ptmalloc_init, &di, &l, NULL) != 0
          && l->l_ns != LM_ID_BASE))
    __morecore = __failing_morecore;
#endif

  thread_arena = &main_arena;

  malloc_init_state (&main_arena);//调用malloc.c中的函数初始化主分配区

#if HAVE_TUNABLES
  TUNABLE_GET (check, int32_t, TUNABLE_CALLBACK (set_mallopt_check));
  TUNABLE_GET (top_pad, size_t, TUNABLE_CALLBACK (set_top_pad));
  TUNABLE_GET (perturb, int32_t, TUNABLE_CALLBACK (set_perturb_byte));
  TUNABLE_GET (mmap_threshold, size_t, TUNABLE_CALLBACK (set_mmap_threshold));
  TUNABLE_GET (trim_threshold, size_t, TUNABLE_CALLBACK (set_trim_threshold));
  TUNABLE_GET (mmap_max, int32_t, TUNABLE_CALLBACK (set_mmaps_max));
  TUNABLE_GET (arena_max, size_t, TUNABLE_CALLBACK (set_arena_max));
  TUNABLE_GET (arena_test, size_t, TUNABLE_CALLBACK (set_arena_test));
# if USE_TCACHE
  TUNABLE_GET (tcache_max, size_t, TUNABLE_CALLBACK (set_tcache_max));
  TUNABLE_GET (tcache_count, size_t, TUNABLE_CALLBACK (set_tcache_count));
  TUNABLE_GET (tcache_unsorted_limit, size_t,
	       TUNABLE_CALLBACK (set_tcache_unsorted_limit));
# endif
#else
  const char *s = NULL;
  if (__glibc_likely (_environ != NULL))
    {
      char **runp = _environ;
      char *envline;
      /*接下来一大堆操作就是这些参数包括
       * MALLOC_TRIM_THRESHOLD_,MALLOC_TOP_PAD_, MALLOC_PERTURB_, MALLOC_MMAP_THRESHOLD_,
       *  MALLOC_CHECK_, MALLOC_MMAP_MAX_, MALLOC_ ARENA_MAX,MALLOC_ ARENA_TEST,
       *
      */
      while (__builtin_expect ((envline = next_env_entry (&runp)) != NULL,
                               0))
        {
          size_t len = strcspn (envline, "=");

          if (envline[len] != '=')
            /* This is a "MALLOC_" variable at the end of the string
               without a '=' character.  Ignore it since otherwise we
               will access invalid memory below.  */
            continue;

          switch (len)
            {
            case 6:
              if (memcmp (envline, "CHECK_", 6) == 0)
                s = &envline[7];
              break;
            case 8:
              if (!__builtin_expect (__libc_enable_secure, 0))
                {
                  if (memcmp (envline, "TOP_PAD_", 8) == 0)
                    __libc_mallopt (M_TOP_PAD, atoi (&envline[9]));
                  else if (memcmp (envline, "PERTURB_", 8) == 0)
                    __libc_mallopt (M_PERTURB, atoi (&envline[9]));
                }
              break;
            case 9:
              if (!__builtin_expect (__libc_enable_secure, 0))
                {
                  if (memcmp (envline, "MMAP_MAX_", 9) == 0)
                    __libc_mallopt (M_MMAP_MAX, atoi (&envline[10]));
                  else if (memcmp (envline, "ARENA_MAX", 9) == 0)
                    __libc_mallopt (M_ARENA_MAX, atoi (&envline[10]));
                }
              break;
            case 10:
              if (!__builtin_expect (__libc_enable_secure, 0))
                {
                  if (memcmp (envline, "ARENA_TEST", 10) == 0)
                    __libc_mallopt (M_ARENA_TEST, atoi (&envline[11]));
                }
              break;
            case 15:
              if (!__builtin_expect (__libc_enable_secure, 0))
                {
                  if (memcmp (envline, "TRIM_THRESHOLD_", 15) == 0)
                    __libc_mallopt (M_TRIM_THRESHOLD, atoi (&envline[16]));
                  else if (memcmp (envline, "MMAP_THRESHOLD_", 15) == 0)
                    __libc_mallopt (M_MMAP_THRESHOLD, atoi (&envline[16]));
                }
              break;
            default:
              break;
            }
        }
    }
  if (s && s[0] != '\0' && s[0] != '0')
    __malloc_check_init ();
#endif

#if HAVE_MALLOC_INIT_HOOK
  void (*hook) (void) = atomic_forced_read (__malloc_initialize_hook);
  if (hook != NULL)
    (*hook)();
#endif
  __malloc_initialized = 1;  //置1表示初始化完毕
}

/* Managing heaps and arenas (for concurrent threads) */

#if MALLOC_DEBUG > 1

/* Print the complete contents of a single heap to stderr. */

static void
dump_heap (heap_info *heap)
{
  char *ptr;
  mchunkptr p;

  fprintf (stderr, "Heap %p, size %10lx:\n", heap, (long) heap->size);
  ptr = (heap->ar_ptr != (mstate) (heap + 1)) ?
        (char *) (heap + 1) : (char *) (heap + 1) + sizeof (struct malloc_state);
  p = (mchunkptr) (((unsigned long) ptr + MALLOC_ALIGN_MASK) &
                   ~MALLOC_ALIGN_MASK);
  for (;; )
    {
      fprintf (stderr, "chunk %p size %10lx", p, (long) p->size);
      if (p == top (heap->ar_ptr))
        {
          fprintf (stderr, " (top)\n");
          break;
        }
      else if (p->size == (0 | PREV_INUSE))
        {
          fprintf (stderr, " (fence)\n");
          break;
        }
      fprintf (stderr, "\n");
      p = next_chunk (p);
    }
}
#endif /* MALLOC_DEBUG > 1 */

/* If consecutive mmap (0, HEAP_MAX_SIZE << 1, ...) calls return decreasing
   addresses as opposed to increasing, new_heap would badly fragment the
   address space.  In that case remember the second HEAP_MAX_SIZE part
   aligned to HEAP_MAX_SIZE from last mmap (0, HEAP_MAX_SIZE << 1, ...)
   call (if it is already aligned) and try to reuse it next time.  We need
   no locking for it, as kernel ensures the atomicity for us - worst case
   we'll call mmap (addr, HEAP_MAX_SIZE, ...) for some value of addr in
   multiple threads, but only one will succeed.  */
static char *aligned_heap_area; //上一次调用 mmap 分配内存的结束虚拟地址

/* Create a new heap.  size is automatically rounded up to a multiple
   of the page size. */
/*
 * New_heap()函数负责从 mmap 区域映射一块内存来作为 sub_heap,映射按HEAP_MAX_SIZE长度对齐的内存,32位为1M,64位为64M
 * 1.调整size合法
 * 2.尝试从aligned_heap_area开始映射空间
 * 3.如果2.失败，则直接映射2*HEAP_MAX_SIZE的空间
 * 4.如果3.失败，则直接映射HEAP_MAX_SIZE的空间
 * 5. 234有一个映射成功了，则申请size的可读写空间，作为申请的模拟堆返回
 */
static heap_info *
new_heap (size_t size, size_t top_pad)
{
  size_t pagesize = GLRO (dl_pagesize);
  char *p1, *p2;
  unsigned long ul;
  heap_info *h;

  if (size + top_pad < HEAP_MIN_SIZE)  //小于最小值时分配最小值,最小32KB
    size = HEAP_MIN_SIZE;
  else if (size + top_pad <= HEAP_MAX_SIZE)  //正常分配
    size += top_pad;
  else if (size > HEAP_MAX_SIZE) //大于最大值,报错
    return 0;
  else
    size = HEAP_MAX_SIZE;
  size = ALIGN_UP (size, pagesize); //对齐

  /* A memory region aligned to a multiple of HEAP_MAX_SIZE is needed.
     No swap space needs to be reserved for the following large
     mapping (on Linux, this is the case for all non-writable mappings
     anyway). */
  p2 = MAP_FAILED;
  if (aligned_heap_area)// aligned_heap_area是上一次调用 mmap 分配内存的结束虚拟地址(已对齐)
    {
      p2 = (char *) MMAP (aligned_heap_area, HEAP_MAX_SIZE, PROT_NONE,
                          MAP_NORESERVE); //尝试从上次映射结束地址开始映射大小为 HEAP_MAX_SIZE 的内存块
      aligned_heap_area = NULL;//论映射是否成功,都将全局变量 aligned_heap_area 设置为 NULL
      if (p2 != MAP_FAILED && ((unsigned long) p2 & (HEAP_MAX_SIZE - 1))) //映射失败 or 未对齐
        {
          __munmap (p2, HEAP_MAX_SIZE); //取消该区域的映射
          p2 = MAP_FAILED;
        }
    }
  if (p2 == MAP_FAILED)
    {
	  /*
	   * aligned_heap_area 为空或者从 aligned_heap_area 开始映射失败了
	   * 尝试映射 2 倍 HEAP_MAX_SIZE 大小的虚拟内存,便于地址对齐,
	   * 最坏可能情况下,需要映射 2 倍 HEAP_MAX_SIZE 大小的虚拟内存才能实现地址按照 HEAP_MAX_SIZE 大小对齐
	   */
      p1 = (char *) MMAP (0, HEAP_MAX_SIZE << 1, PROT_NONE, MAP_NORESERVE);
      if (p1 != MAP_FAILED)
        {
          p2 = (char *) (((unsigned long) p1 + (HEAP_MAX_SIZE - 1))
                         & ~(HEAP_MAX_SIZE - 1));  //申请成功将对齐之后的第一个地址返回给p2
          ul = p2 - p1;
          if (ul)
            __munmap (p1, ul); //释放掉中间的无用的虚拟内存
          else
            aligned_heap_area = p2 + HEAP_MAX_SIZE; //p2 -> p2+HEAP_MAX_SIZE 之间就是此次申请的subheap,
          __munmap (p2 + HEAP_MAX_SIZE, HEAP_MAX_SIZE - ul);//释放掉后面的无用的虚拟内存
        }
      else //映射 2 倍 HEAP_MAX_SIZE 大小的虚拟内存失败了
        {
          /* Try to take the chance that an allocation of only HEAP_MAX_SIZE
             is already aligned. */
          p2 = (char *) MMAP (0, HEAP_MAX_SIZE, PROT_NONE, MAP_NORESERVE); //再尝试映射 HEAP_MAX_SIZE 大小的
          if (p2 == MAP_FAILED) //再次失败,返回
            return 0;

          if ((unsigned long) p2 & (HEAP_MAX_SIZE - 1))  //没对齐,返回
            {
              __munmap (p2, HEAP_MAX_SIZE);
              return 0;
            }
        }
    }
  if (__mprotect (p2, size, PROT_READ | PROT_WRITE) != 0)  //将 size 大小的堆设置为可读可写,如果失败,解除整个 sub_heap的映射
    {
      __munmap (p2, HEAP_MAX_SIZE);
      return 0;
    }
  h = (heap_info *) p2;  //作为模拟堆返回
  h->size = size;
  h->mprotect_size = size;
  LIBC_PROBE (memory_heap_new, 2, h, h->size);
  return h;
}

/* Grow a heap.  size is automatically rounded up to a
   multiple of the page size. */

static int
grow_heap (heap_info *h, long diff)
{
  size_t pagesize = GLRO (dl_pagesize);
  long new_size;

  diff = ALIGN_UP (diff, pagesize);  //将要增加的内存按页对齐
  new_size = (long) h->size + diff;  //计算新的大小
  if ((unsigned long) new_size > (unsigned long) HEAP_MAX_SIZE) //新增之后大于最大大小直接退出
    return -1;

  if ((unsigned long) new_size > h->mprotect_size)  //判断 new_size 是否大于当前 sub_heap 的可读可写区域大小
    {
      if (__mprotect ((char *) h + h->mprotect_size,
                      (unsigned long) new_size - h->mprotect_size,
                      PROT_READ | PROT_WRITE) != 0)  //设置新增区域可读可写
        return -2;

      h->mprotect_size = new_size;	//更新
    }

  h->size = new_size; //更新size
  LIBC_PROBE (memory_heap_more, 2, h, h->size);
  return 0;
}

/* Shrink a heap.  */

static int
shrink_heap (heap_info *h, long diff) //diff已经对齐
{
  long new_size;

  new_size = (long) h->size - diff;
  if (new_size < (long) sizeof (*h)) //收缩后空间大小不能比模拟堆的结构体还小
    return -1;

  /* Try to re-map the extra heap space freshly to save memory, and make it
     inaccessible.  See malloc-sysdep.h to know when this is true.  */
  if (__glibc_unlikely (check_may_shrink_heap ())) //函数运行在非Glibc中
    {
      if ((char *) MMAP ((char *) h + new_size, diff, PROT_NONE,
                         MAP_FIXED) == (char *) MAP_FAILED)
        return -2;

      h->mprotect_size = new_size;
    }
  else
    __madvise ((char *) h + new_size, diff, MADV_DONTNEED);//函数运行在 Glibc 库中,则调用 madvise()函数,实际上 madvise()函数什么也不做,只是返回错误
  /*fprintf(stderr, "shrink %p %08lx\n", h, new_size);*/

  h->size = new_size;
  LIBC_PROBE (memory_heap_less, 2, h, h->size);
  return 0;
}

/* Delete a heap. */
/*
 * 判 断 当 前 删 除 的 sub_heap 的 结 束 地 址 是 否 与 全 局 变 量 aligned_heap_area 指向的地址相同,如果相同,
 * 则将全局变量 aligned_heap_area 设置为 NULL,
 * 因为当前 sub_heap 删除以后,就可以从当前 sub_heap 的起始地址或是更低的地址开始映射新的 sub_heap,这样可以尽量从地地址映射内存
 */
#define delete_heap(heap) \
  do {									      \
      if ((char *) (heap) + HEAP_MAX_SIZE == aligned_heap_area)		      \
        aligned_heap_area = NULL;					      \
      __munmap ((char *) (heap), HEAP_MAX_SIZE);			      \
    } while (0)
/*
 * 每个非主分配区至少有一个 sub_heap,每个非主分配区的第一个 sub_heap 中包含了一
 * 个 heap_info 的实例和 malloc_state 的实例,分主分配区中的其它 sub_heap 中只有一个
 * heap_info 实例,紧跟 heap_info 实例后,为可以用于分配的内存块。
 *
 * 当前非主分配区的 top chunk 与当前 sub_heap 的 heap_info 实例的结束地址相同时,
 * 意味着当前 sub_heap 中只有一个空闲 chunk,没有已分配的 chunk。
 * 所以可以将当前整个 sub_heap 都释放掉。
 *
 *
 *
 *    主分配区
    +====================+ 高地址
        chunk
    +====================+
      heap_info
    +====================+ next_heap
        2*SIZE_SZ|1   (size)
    ---------------------
              0		(prev_size)
    +====================+ fencepost_chunk2
		2*SIZE_SZ   (size)
	---------------------
		prev_size  (prev_size)
    +====================+ fencepost_chunk1
       topchunk
    +====================+
        chunk
    +====================+
      heap_info
    +====================+ heap


    非主分配区
    +====================+ 高地址
        chunk
    +====================+
      heap_info
    +====================+ next_heap
        0|1       (size)
    ---------------------
      2*SIZE_SZ (prev_size)
    +====================+ fencepost_chunk2
      2*SIZE_SZ (size)
    ----------------------
     prev_size(prev_size)
    +====================+ fencepost_chunk1
       topchunk
    +====================+
        chunk
    +====================+
      heap_info
    +====================+ heap
 *
 *
 */
static int
heap_trim (heap_info *heap, size_t pad)
{
  mstate ar_ptr = heap->ar_ptr;
  unsigned long pagesz = GLRO (dl_pagesize);
  mchunkptr top_chunk = top (ar_ptr), p, bck, fwd;
  heap_info *prev_heap;
  long new_size, top_size, top_area, extra, prev_size, misalign;

  /* Can this heap go away completely? */
 while (top_chunk == chunk_at_offset (heap, sizeof (*heap)))  //	,表明该空sub heap完全空闲,可直接完全释放掉
    {
      prev_heap = heap->prev;
      prev_size = prev_heap->size - (MINSIZE - 2 * SIZE_SZ);
      p = chunk_at_offset (prev_heap, prev_size);//fencepost的第二个chunk
      /* fencepost must be properly aligned.  */
      misalign = ((long) p) & MALLOC_ALIGN_MASK;//
      p = chunk_at_offset (prev_heap, prev_size - misalign);//对齐
      assert (chunksize_nomask (p) == (0 | PREV_INUSE)); /* must be fencepost */ //通过关键位以确定是fencepost的第二个chunk
      p = prev_chunk (p);//指向fencepost第一个chunk
      new_size = chunksize (p) + (MINSIZE - 2 * SIZE_SZ) + misalign;  //fencepost的第一个chunk+第二个chunk的大小
      assert (new_size > 0 && new_size < (long) (2 * MINSIZE));
      if (!prev_inuse (p)) //前一个空闲  , new_size 表示当前模拟堆的前一个模拟堆中可读可写区域的可用空间
        new_size += prev_size (p);  //加入
      assert (new_size > 0 && new_size < HEAP_MAX_SIZE);
      if (new_size + (HEAP_MAX_SIZE - prev_heap->size) < pad + MINSIZE + pagesz) //如果前一个模拟堆的空闲空间太小，则不能释放当前堆（避免再次新建模拟堆）
        break;
      ar_ptr->system_mem -= heap->size;  //开始释放,更新当前非主分配区已分配的内存大小
      LIBC_PROBE (memory_heap_free, 2, heap, heap->size);  //按照代码中的宏定义，其实这句话什么也没有干。
      delete_heap (heap);//释放当前模拟堆
      heap = prev_heap;//heap指向前一个模拟堆
      if (!prev_inuse (p)) /* consolidate backward */  //p目前指向前一个堆的倒数第二个chunk,循环删除以保证不能有连续两个空闲的chunk.
        {
          p = prev_chunk (p);//
          unlink (ar_ptr, p, bck, fwd);
        }
      assert (((unsigned long) ((char *) p + new_size) & (pagesz - 1)) == 0); //确保对齐
      assert (((char *) p + new_size) == ((char *) heap + heap->size));  //???? 這個斷言沒有看懂
      top (ar_ptr) = top_chunk = p; //修改topchunk的指針
      set_head (top_chunk, new_size | PREV_INUSE); //更新topchunk的size
      /*check_chunk(ar_ptr, top_chunk);*/
    }

  /* Uses similar logic for per-thread arenas as the main arena with systrim
     and _int_free by preserving the top pad and rounding down to the nearest
     page.  */
  top_size = chunksize (top_chunk);
  if ((unsigned long)(top_size) <
      (unsigned long)(mp_.trim_threshold)) //topchunk还没有达到收缩阈值
    return 0;

  top_area = top_size - MINSIZE - 1; //topchunk太小也退出
  if (top_area < 0 || (size_t) top_area <= pad)
    return 0;

  /* Release in pagesize units and round down to the nearest page.  */
  extra = ALIGN_DOWN(top_area - pad, pagesz);  // 计算需要收缩的空间
  if (extra == 0)
    return 0;

  /* Try to shrink. */
  if (shrink_heap (heap, extra) != 0)
    return 0;

  ar_ptr->system_mem -= extra;  //更新统计

  /* Success. Adjust top accordingly. */
  set_head (top_chunk, (top_size - extra) | PREV_INUSE); //更新topchunk在收缩后的大小
  /*check_chunk(ar_ptr, top_chunk);*/
  return 1;
}

/* Create a new arena with initial size "size".  */

/* If REPLACED_ARENA is not NULL, detach it from this thread.  Must be
   called while free_list_lock is held.  */
static void
detach_arena (mstate replaced_arena)
{
  if (replaced_arena != NULL)
    {
      assert (replaced_arena->attached_threads > 0);
      /* The current implementation only detaches from main_arena in
	 case of allocation failure.  This means that it is likely not
	 beneficial to put the arena on free_list even if the
	 reference count reaches zero.  */
      --replaced_arena->attached_threads;
    }
}
/*
 * 创建一个新的分配区,由arena_get2调用
 */
static mstate
_int_new_arena (size_t size)
{
	/*
	 * 对于一个新的非主分配区,至少包含一个 sub_heap,每个非主分配区中都有相应的管
	 * 理数据结构,每个非主分配区都有一个 heap_info 实例和 malloc_state 的实例,这两个实例
	 * 都位于非主分配区的第一个 sub_heap 的开始部分,heap_info 实例后面紧接着 malloc_state 实例
	 */
  mstate a;
  heap_info *h;
  char *ptr;
  unsigned long misalign;

  h = new_heap (size + (sizeof (*h) + sizeof (*a) + MALLOC_ALIGNMENT),
                mp_.top_pad);  //返回一个sub_heap,
  if (!h)
    {
      /* Maybe size is too large to fit in a single heap.  So, just try
         to create a minimally-sized arena and let _int_malloc() attempt
         to deal with the large request via mmap_chunk().  */
      h = new_heap (sizeof (*h) + sizeof (*a) + MALLOC_ALIGNMENT, mp_.top_pad);
      if (!h)
        return 0;
    }
  a = h->ar_ptr = (mstate) (h + 1); //紧跟着一个malloc_state实例
  malloc_init_state (a); //初始化分配区
  a->attached_threads = 1; //
  /*a->next = NULL;*/
  a->system_mem = a->max_system_mem = h->size; //更新该分配区所分配的内存大小的统计值

  /* Set up the top chunk, with proper alignment. */
  ptr = (char *) (a + 1);
  misalign = (unsigned long) chunk2mem (ptr) & MALLOC_ALIGN_MASK; //对齐
  if (misalign > 0)
    ptr += MALLOC_ALIGNMENT - misalign;
  /*
   * 把 sub_heap 中整个空闲内存块作为 top chunk,然后设置 top chunk 的 size,
   * 并标识 top chunk 的前一个 chunk 为已处于分配状态。
   */
  top (a) = (mchunkptr) ptr;
  set_head (top (a), (((char *) h + h->size) - ptr) | PREV_INUSE);

  LIBC_PROBE (memory_arena_new, 2, a, size);
  mstate replaced_arena = thread_arena;
  thread_arena = a; //设置thread_arena为当前创建的分配区
  __libc_lock_init (a->mutex);  //初始化锁

  __libc_lock_lock (list_lock); //获得该锁

  /* Add the new arena to the global list.  */
  /*
   * 接下来三步,把该非主分配区加入到分配区的链表中
   */
  a->next = main_arena.next;
  /* FIXME: The barrier is an attempt to synchronize with read access
     in reused_arena, which does not acquire list_lock while
     traversing the list.  */
  atomic_write_barrier ();
  main_arena.next = a;

  __libc_lock_unlock (list_lock);

  __libc_lock_lock (free_list_lock);
  detach_arena (replaced_arena);
  __libc_lock_unlock (free_list_lock);

  /* Lock this arena.  NB: Another thread may have been attached to
     this arena because the arena is now accessible from the
     main_arena.next list and could have been picked by reused_arena.
     This can only happen for the last arena created (before the arena
     limit is reached).  At this point, some arena has to be attached
     to two threads.  We could acquire the arena lock before list_lock
     to make it less likely that reused_arena picks this new arena,
     but this could result in a deadlock with
     __malloc_fork_lock_parent.  */

  __libc_lock_lock (a->mutex);

  return a;
}


/* Remove an arena from free_list.  */
static mstate
get_free_list (void)
{
  mstate replaced_arena = thread_arena;
  mstate result = free_list;
  if (result != NULL) //free_list不为空
    {
      __libc_lock_lock (free_list_lock); //加锁
      result = free_list;
      if (result != NULL)
	{
	  free_list = result->next_free;   //遍历空闲分配区组成的链表

	  /* The arena will be attached to this thread.  */
	  assert (result->attached_threads == 0);  //是否有线程已经占用
	  result->attached_threads = 1;  //置1

	  detach_arena (replaced_arena);
	}
      __libc_lock_unlock (free_list_lock);//释放锁

      if (result != NULL)
        {
          LIBC_PROBE (memory_arena_reuse_free_list, 1, result);
          __libc_lock_lock (result->mutex);
          thread_arena = result;  //把结果放入线程的私有实例中
        }
    }

  return result;
}

/* Remove the arena from the free list (if it is present).
   free_list_lock must have been acquired by the caller.  */
static void
remove_from_free_list (mstate arena)
{
  mstate *previous = &free_list;
  for (mstate p = free_list; p != NULL; p = p->next_free)
    {
      assert (p->attached_threads == 0);
      if (p == arena)
	{
	  /* Remove the requested arena from the list.  */
	  *previous = p->next_free;
	  break;
	}
      else
	previous = &p->next_free;
    }
}

/* Lock and return an arena that can be reused for memory allocation.
   Avoid AVOID_ARENA as we have already failed to allocate memory in
   it and it is currently locked.  */
static mstate
reused_arena (mstate avoid_arena)
{
  mstate result;
  /* FIXME: Access to next_to_use suffers from data races.  */
  static mstate next_to_use;//next_to_use 指向下一个可能可用的分配区,
  	  	  	  	  	  	    //主要用于记录上次遍历分配区循环链表到达的位置,避免每次都从同一个分配区开始遍历
  if (next_to_use == NULL) //首先判断 next_to_use 是否为 NULL,如果是,将主分配区赋值给 next_to_use
    next_to_use = &main_arena;

  /* Iterate over all arenas (including those linked from
     free_list).  */
  result = next_to_use;
  do //开始遍历所有分配区,直至遍历完了一遍
    {
      if (!__libc_lock_trylock (result->mutex))  //尝试加锁
        goto out;

      /* FIXME: This is a data race, see _int_new_arena.  */
      result = result->next;
    }
  while (result != next_to_use);

  /* Avoid AVOID_ARENA as we have already failed to allocate memory
     in that arena and it is currently locked.   */
  if (result == avoid_arena)
    result = result->next;

  /* No arena available without contention.  Wait for the next in line.  */
  LIBC_PROBE (memory_arena_reuse_wait, 3, &result->mutex, result, avoid_arena); //之前的尝试都失败了,则等待获得 next_to_use 指向的分配区的锁
  __libc_lock_lock (result->mutex);

out:   //进入到out,代表着已经成功获得一个分配区的锁
  /* Attach the arena to the current thread.  */
  {
    /* Update the arena thread attachment counters.   */
    mstate replaced_arena = thread_arena;
    __libc_lock_lock (free_list_lock);
    detach_arena (replaced_arena);

    /* We may have picked up an arena on the free list.  We need to
       preserve the invariant that no arena on the free list has a
       positive attached_threads counter (otherwise,
       arena_thread_freeres cannot use the counter to determine if the
       arena needs to be put on the free list).  We unconditionally
       remove the selected arena from the free list.  The caller of
       reused_arena checked the free list and observed it to be empty,
       so the list is very short.  */
    remove_from_free_list (result);  // 从空闲分配区链表移除,保证在链表中的分配区的attached_threads计数器

    ++result->attached_threads; // 更新计数器

    __libc_lock_unlock (free_list_lock);
  }

  LIBC_PROBE (memory_arena_reuse, 2, result, avoid_arena);  //什么都没干..
  thread_arena = result;  //把这个分配区绑定到线程的私有实例
  next_to_use = result->next;

  return result;
}
/*
 * arena_get 宏尝试查看线程的私用实例中是否包含一个分配区,如果
 * 不存在分配区或是存在分配区,但对该分配区加锁失败,就会调用 arena_get2()函数获得一个分配区
 */
static mstate
arena_get2 (size_t size, mstate avoid_arena)
{
  mstate a;

  static size_t narenas_limit; //分配区最大数量

  a = get_free_list (); //尝试从空闲分配区链表获取一个分配区
  if (a == NULL)  //没有获取到
    {
      /* Nothing immediately available, so generate a new arena.  */
      if (narenas_limit == 0)
        {
          if (mp_.arena_max != 0)
            narenas_limit = mp_.arena_max;
          else if (narenas > mp_.arena_test)
            {
              int n = __get_nprocs ();

              if (n >= 1)
                narenas_limit = NARENAS_FROM_NCORES (n);
              else
                /* We have no information about the system.  Assume two
                   cores.  */
                narenas_limit = NARENAS_FROM_NCORES (2);
            }
        }
    repeat:;
      size_t n = narenas; //分配区数量
      /* NB: the following depends on the fact that (size_t)0 - 1 is a
         very large number and that the underflow is OK.  If arena_max
         is set the value of arena_test is irrelevant.  If arena_test
         is set but narenas is not yet larger or equal to arena_test
         narenas_limit is 0.  There is no possibility for narenas to
         be too big for the test to always fail since there is not
         enough address space to create that many arenas.  */
      if (__glibc_unlikely (n <= narenas_limit - 1))
        {
          if (catomic_compare_and_exchange_bool_acq (&narenas, n + 1, n))  //narenas原子自加1,表示新建分配区
            goto repeat;
          a = _int_new_arena (size);  //创建一个新的分配区
	  if (__glibc_unlikely (a == NULL))
            catomic_decrement (&narenas);
        }
      else
        a = reused_arena (avoid_arena); //重用分配区
    }
  return a;
}

/* If we don't have the main arena, then maybe the failure is due to running
   out of mmapped areas, so we can try allocating on the main arena.
   Otherwise, it is likely that sbrk() has failed and there is still a chance
   to mmap(), so try one of the other arenas.  */
static mstate
arena_get_retry (mstate ar_ptr, size_t bytes)
{
  LIBC_PROBE (memory_arena_retry, 2, bytes, ar_ptr);
  if (ar_ptr != &main_arena) //不是主分配区
    {
      __libc_lock_unlock (ar_ptr->mutex);//解锁当前的分配区,
      ar_ptr = &main_arena;//从主分配区尝试
      __libc_lock_lock (ar_ptr->mutex);//获取主分配区的锁
    }
  else
    {
      __libc_lock_unlock (ar_ptr->mutex); //解锁主分配区
      ar_ptr = arena_get2 (bytes, ar_ptr);//尝试从其他分配区获取
    }

  return ar_ptr;
}

static void __attribute__ ((section ("__libc_thread_freeres_fn")))
arena_thread_freeres (void)
{
  /* Shut down the thread cache first.  This could deallocate data for
     the thread arena, so do this before we put the arena on the free
     list.  */
  tcache_thread_shutdown ();

  mstate a = thread_arena;
  thread_arena = NULL;

  if (a != NULL)
    {
      __libc_lock_lock (free_list_lock);
      /* If this was the last attached thread for this arena, put the
	 arena on the free list.  */
      assert (a->attached_threads > 0);
      if (--a->attached_threads == 0)
	{
	  a->next_free = free_list;
	  free_list = a;
	}
      __libc_lock_unlock (free_list_lock);
    }
}
text_set_element (__libc_thread_subfreeres, arena_thread_freeres);

/*
 * Local variables:
 * c-basic-offset: 2
 * End:
 */
