/*
 * mm.c
 *
 * Wang Ziqi 2100013093
 * 
 * Segregated free list with segregated fit
 * remove footer in allocated blocks
 * maintain list with LIFO method
 * first-fit search
 * refine realloc operation,avoid new allocation if possible
 * 
 * ******free block structure****** similar to image 9-48(CSAPP 603)
 * 
 * //Header: block size | 0 | PREVALLOC | 0(ALLOC)  4 bytes
 * ---------------------------------------------
 * //Previous block pointer(in list)  4 bytes  |
 * //Next block pointer(in list)  4 bytes      |    <------- valid block space
 * //Free space                                |
 * ---------------------------------------------
 * //Padding(optional)
 * //Footer: block size | 0 | PREVALLOC | 0(ALLOC)  4 bytes
 * 
 * 
 * ******allocated block structure****** use 1 bit(PREVALLOC) in header to remove footer
 * 
 * //Header: block size | 0 | PREVALLOC | 1(ALLOC)  4 bytes
 * //Valid block space (4 bytes minimum)
 * //Padding(optional)
 * 
 * 
 * 
 */
#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "./mm.h"
#include "./memlib.h"


// Header/footer printing macros
#define PACK_FMT "(%#x, %s, %s)"
#define PACK_ARG(p) \
  GET_SIZE(p), GET_PREVALLOC(p) ? "ALLOC" : "FREE", GET_ALLOC(p) ? "ALLOC" : "FREE"

// DEBUG may be defined in Makefile
#ifdef DEBUG
#define dbg_printf(FORMAT, ...) \
  printf("%s(%d): " FORMAT "\n", __func__, __LINE__, ##__VA_ARGS__)

#define CHECK_HEAP() my_checkheap(__func__, __LINE__)
#else
#define dbg_printf(...)
#define CHECK_HEAP()
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

#define ALIGNMENT 8

#define ALIGN(p) (((size_t)(p) + ((ALIGNMENT)-1)) & ~0x7)

/************Macros************/

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */ 

// Basic types and sizes
typedef uint32_t WORD;   ///< WORD is 32-bit
typedef uint64_t DWORD;  ///< DWORD (double WORD) is 64-bit

#define MAX(x, y) ((x) > (y) ? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))
/* Pack a size and allocated info into a word */
#define PACK(size, allocinfo)  ((size) | (allocinfo)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_PREVALLOC(p) (GET(p) & 0x2)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_ALLOCINFO(p) (GET(p) & 0x7)

/* modify prevalloc bit*/
#define SET_PREVALLOC(p) (GET(p) |= 0x2)
#define CLEAR_PREVALLOC(p) (GET(p) &= ~0x2)

/// btag enums
#define PREV_KEEP ((WORD)(-1)) 
#define PREV_ALLOC 0x2          
#define NO_PREV 0x0           

/* Given block p bp, compute address of its header and footer */
#define HDRP(bp) ((void*)((char*)(bp)-WSIZE))
#define FTRP(bp) ((void*)((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE))

/* Given block p bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((void *)((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))) 
#define PREV_BLKP(bp)  ((void *)((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))) 


/// Get the address of next/previous free block using segregated_list
#define GET_NEXT_FREE(bp)          \
  ({                               \
    WORD val = GET(bp);       \
    val ? val + heap : NULL; \
  })
#define GET_PREV_FREE(bp)                         \
  ({                                              \
    WORD val = GET((char*)(bp) + WSIZE); \
    val ? val + heap : NULL;                \
  })
#define SET_NEXT_FREE(bp, val) \
  PUT((bp), (WORD)((val) ? ((char*)(val)-heap) : 0))
#define SET_PREV_FREE(bp, val)      \
  PUT((char*)(bp) + WSIZE, \
           (WORD)((val) ? ((char*)(val)-heap) : 0))

/// Automatic choose appropriate segregated_list id
#define SEGLIST_AUTO ((size_t)-1)

#define LIST_SIZE 13

/// The begin position of available heap ( @c bp of prologue)
static char* heap = NULL;

/// Array of seglists
static void** segregated_list;

// Helper function declarations

static void* extend_heap(size_t);
static void* coalesce(void*);
static void* find_fit(size_t);
static void place(void*, size_t);

void my_checkheap(const char*, int);

static int list_num(size_t);
static void list_insert(void*, size_t);
static void list_delete(void*, size_t);


static inline void* get_prev_free(void* bp)
{
    WORD val = GET(bp);
    void *prev = NULL;
    if(val){
      prev = (void*)(heap + val);
    }
    return prev;
}

static inline void* get_next_free(void* bp)
{
    WORD val = GET((char*)bp + WSIZE);
    void *succ = NULL;
    if(val){
      succ = (void*)(heap + val);
    }
    return succ;
}

static inline void set_prev_free(void *bp,void *lp)
{
  WORD val = 0;
  if(lp){
    val = (char*)lp - heap;
  }
  PUT(bp,val);
}

static inline void set_next_free(void *bp,void *np)
{
  WORD val = 0;
  if(np){
    val = (char*)np - heap;
  }
  PUT((char*)bp + WSIZE,val);
}
/*
 * Initialize: return -1 on error, 0 on success.
 * Put segregated list at the beginning of the heap
 * extend the heap with a 4096-byte block 
 */
int mm_init(void) {
    if ((heap = mem_sbrk(LIST_SIZE * DSIZE + 4 * WSIZE)) == (void*)-1)
    return -1;
    segregated_list = (void**)heap;
    for (int i = 0; i < LIST_SIZE; i++) {
        segregated_list[i] = NULL;
    }
    /*now heap points to the first bit after segregated list*/
    heap = (char*)(segregated_list + LIST_SIZE);
    PUT(heap, 0);                                             /* Alignment padding */
    PUT(heap + 1*WSIZE, PACK(DSIZE, 1));/* Prologue header */
    PUT(heap + 2*WSIZE, PACK(DSIZE, 1));/* Prologue footer */ 
    PUT(heap + 3*WSIZE, PACK(0, 3));         /* Epilogue header */
    heap += DSIZE;

    /* Extend the heap with a block initially*/
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) 
        return -1;
    return 0;
}

/*
 * malloc
 */
void* malloc(size_t size) {
  size_t asize;
  void* bp;
  if (size == 0) return NULL;

  if (size == 448) size = 512;
  if (size <= DSIZE)
    asize = 2*DSIZE;
  else
    asize = ALIGN(WSIZE + size);
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }
  size_t extendsize = MAX(asize, CHUNKSIZE);
  /* No fit found. Get more memory and place the block */               
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)  
        return NULL;                                  
    place(bp, asize);                                 
    return bp;
}

/*
 * free
 */
void free(void* p) {
    if (!p) return;
    size_t size = GET_SIZE(HDRP(p));
    if(GET_PREVALLOC(HDRP(p))){//prev allocated
        PUT(HDRP(p),PACK(size,2));
        PUT(FTRP(p),PACK(size,2));
    }
    else{
        PUT(HDRP(p),PACK(size,0));
        PUT(HDRP(p),PACK(size,0));
    }

    void* next_block = NEXT_BLKP(p);
    CLEAR_PREVALLOC(HDRP(next_block));
    coalesce(p);
}

/*
 * realloc: Multiple cases,will it work better than simply mallocing a new block?
 * Inspired by Writeup
 * 
 * case 1: size == 0.free(oldptr)
 * case 2: oldptr == NULL.malloc(size)
 * case 3: size <= oldsize
 *      branch 1: the result of (oldsize - size)can't reach smallest block size.just return oldptr
 *      branch 2: the original block could be split into two valid blocks.split it and return oldptr
 * csae 4: size > oldsize
 *      branch 1: there is a free block after the original block,coalesce them may fit our needs.
 *      branch 2: the original block is the last block in heap.extend the block with extend_heap()
 *                then goto branch 1.
 *      default: have no choice!malloc a new block and free the original one
 */
void* realloc(void* oldptr, size_t size) {
  if (size == 0) {
    free(oldptr);
    return NULL;
  }
  if (oldptr == NULL) {
    return malloc(size);
  }
  
  size_t oldsize;
  size_t asize;
  
  oldsize = GET_SIZE(HDRP(oldptr));

    if(size <= 8)
        asize = 16;
    else
        asize = ALIGN(size + 4);
  
  int dval = (int)asize - (int)oldsize;
   /* case 3: size <= oldsize*/
  if(dval <= 0){
  	if(dval > -16)//branch 1
  		return oldptr;
  	else{//branch 2
        /*renew size of original block*/
  		PUT(HDRP(oldptr),PACK(asize,GET_ALLOCINFO(HDRP(oldptr))));
  		void *np = NEXT_BLKP(oldptr);
        /*set newly split block free*/
  		PUT(HDRP(np),PACK(-dval,2));
        PUT(FTRP(np),PACK(-dval,2));
  		CLEAR_PREVALLOC(HDRP(NEXT_BLKP(np)));
  		list_insert(np,-dval);
  		return oldptr;
  	}
  }
  /* case 4: size > oldsize*/
  else{
  	void *np = NEXT_BLKP(oldptr);
        if(np > mem_heap_hi()){//branch 2,heap boundary should be checked first.
            np = extend_heap(dval/WSIZE);
        }
        if(!GET_ALLOC(HDRP(np))){
            size_t newsize = GET_SIZE(HDRP(np));
            int sizeok = (int)oldsize + (int)newsize - (int)asize;
            if(sizeok >= 0){//enough size!
            /*coalesce two blocks*/
                list_delete(np,newsize);
                if(sizeok < 2*DSIZE){//cant be split
             	      PUT(HDRP(oldptr),PACK((oldsize + newsize),GET_ALLOCINFO(HDRP(oldptr))));
                    SET_PREVALLOC(HDRP(NEXT_BLKP(oldptr)));
                    return oldptr;
                }
                else{//can be split
                    PUT(HDRP(oldptr),PACK(asize,GET_ALLOCINFO(HDRP(oldptr))));

                    void *nnp = NEXT_BLKP(oldptr);
                    PUT(HDRP(nnp),PACK(sizeok,2));
                    PUT(FTRP(nnp),PACK(sizeok,2));
                    CLEAR_PREVALLOC(HDRP(NEXT_BLKP(nnp)));
                    list_insert(nnp,sizeok);
                    return oldptr;
                }
            }
        
       
        }
  }
  
  void* newptr;
  if ((newptr = malloc(size)) == NULL) return NULL;
  memcpy(newptr, oldptr, MIN(size, GET_SIZE(HDRP(oldptr))));
  free(oldptr);
  return newptr;
}

/*
 * calloc - you may want to look at mm-naive.c
 * This function is not tested by mdriver, but it is
 * needed to run the traces.
 */
void *calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
    void *newptr;

    newptr = malloc(bytes);
    memset(newptr, 0, bytes);

    return newptr;
}

void mm_checkheap(int lineno) {}  // Shut up linker complaint.


/*
 * Extend heap: Extend heap by adding a free block
 * Return pointer to the block
 * Coalesce with previous block if possible,insert happens in this step
 */
static inline void* extend_heap(size_t words) {
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = ((words % 2) ? (words + 1)* WSIZE : words* WSIZE) ;
    if (size < 2*DSIZE) size = 2*DSIZE;

    if ((bp = mem_sbrk(size)) == (void*)-1) 
        return NULL;
    if(GET_PREVALLOC(HDRP(bp))){//prev allocated
        PUT(HDRP(bp),PACK(size,2));
        PUT(FTRP(bp),PACK(size,2));
    }
    else{
        PUT(HDRP(bp),PACK(size,0));
        PUT(HDRP(bp),PACK(size,0));
    }
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));/*new epilogue header*/
    CLEAR_PREVALLOC(HDRP(NEXT_BLKP(bp)));

    return coalesce(bp);
}

/*
 * Coalesce: coalesce free blocks
 * 
 * 
 */
static void* coalesce(void* bp) {
    int prev_alloc = GET_PREVALLOC(HDRP(bp));
    int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    size_t size = GET_SIZE(HDRP(bp));
    if (prev_alloc && next_alloc) {//can't merge
        
    } 
    else if (prev_alloc && !next_alloc) {//merge with next block
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size += next_size;
        list_delete(NEXT_BLKP(bp), next_size);
        PUT(HDRP(bp), PACK(size, (2)));
        PUT(FTRP(bp), PACK(size, (2)));
    } 
    else if (!prev_alloc && next_alloc) {//merge with prev block
        size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
        size += prev_size;
        list_delete(PREV_BLKP(bp), prev_size);
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, (GET_ALLOCINFO(HDRP(bp)))));
        PUT(FTRP(bp), PACK(size, (GET_ALLOCINFO(HDRP(bp)))));
    }
        else {//merge with prev and next
        size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
        size += next_size + prev_size;
        list_delete(NEXT_BLKP(bp), next_size);
        list_delete(PREV_BLKP(bp), prev_size);
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, (GET_ALLOCINFO(HDRP(bp)))));
        PUT(FTRP(bp), PACK(size, (GET_ALLOCINFO(HDRP(bp)))));
    }
    /* final insert */
    list_insert(bp, size);
    return bp;
}

/*
 * Find fit: find a block for asize-byte allocation
 * first-fit method
 */
static inline void *find_fit(size_t asize)
{
    int id = list_num(asize);
    /* First-fit search */
    void *bp;
    while (id < LIST_SIZE)
    {
        for (bp = segregated_list[id]; bp != NULL; bp = get_next_free(bp))
        {
            if (asize <= GET_SIZE(HDRP(bp)))
            {
                return bp;
            }
        }
        id++;
    }
    return NULL; /* No fit */
}

/*
 * place: place a block of asize bytes at bp
 * split if possible
 * 
 */
static void place(void* bp, size_t asize) {
  size_t csize = GET_SIZE(HDRP(bp));   
    list_delete(bp,csize);
    long long x = csize - asize;
    if (x >= (2*DSIZE)) { //can split
        PUT(HDRP(bp), PACK(asize, 1 | GET_ALLOCINFO(HDRP(bp))));
        
        /*new free block*/
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(x, 2));
        PUT(FTRP(bp), PACK(x, 2));
        list_insert(bp,x);
    }
    else { //cant split
        PUT(HDRP(bp), PACK(csize, 1 | GET_ALLOCINFO(HDRP(bp))));

        /*renew next block*/
        SET_PREVALLOC(HDRP(NEXT_BLKP(bp)));
    }
}


/*
 * Get list id: return proper list id according to allocated size
 * Devided by powers of 2
 * Assume asize is aligned
 */
static inline int list_num(size_t asize)
{
    // if(asize % ALIGNMENT){
    //     dbg_printf("asize is not aligned!");
    // }

    if(asize <= 16){
        return 0;
    }
    if(asize <= 32){
        return 1;
    }
    if(asize <= 64){
        return 2;
    }
    if(asize <= 128){
        return 3;
    }
    if(asize <= 256){
        return 4;
    }
    if(asize <= 512){
        return 5;
    }
    if(asize <= 1024){
        return 6;
    }
    if(asize <= 2048){
        return 7;
    }
    if(asize <= 4096){
        return 8;
    }
    if(asize <= 8192){
        return 9;
    }
    if(asize <= 16384){
        return 10;
    }
    if(asize <= 32768){
        return 11;
    }
    return 12;
}

/*
 * List insert: insert a free block to proper list
 * insert at head.
 */
static void list_insert(void* fp, size_t size) {
  int id = list_num(size);
  void *list = segregated_list[id];
  if (list) {  // list not empty
    set_prev_free(list, fp);
  }
  set_next_free(fp, list);
  set_prev_free(fp, NULL);
  segregated_list[id] = fp;
}

/*
 * List delete: delete a block from list
 *
 */
static void list_delete(void* bp, size_t size) {
  size_t id = list_num(size);
  char* next = get_next_free(bp);
  char* prev = get_prev_free(bp);
  if (prev) {
    set_next_free(prev, next);
  } else {
    segregated_list[id] = next;
  }
  if (next) {
    set_prev_free(next, prev);
  }
}


/*
 * Return whether the pointer is in the heap.
 * May be useful for debugging.
 */
static int in_heap(const void* p) {
  return p <= mem_heap_hi() && p >= mem_heap_lo();
}

/*
 * Return whether the pointer is aligned.
 * May be useful for debugging.
 */
static int aligned(const void* p) { return (size_t)ALIGN(p) == (size_t)p; }

/**
 * @brief Heap consistency checker
 * Scans the heap and checks it for correctness, call it by @c CHECK_HEAP
 * **For Teacher Assistants / Instructors**
 *   I use this function instead of default @c mm_checkheap
 *   because I prefer passing @c __func__ than @c __LINE__ .
 * @param func Pass @c __func__ into it for debugging
 * @param lineno Pass @c __LINE__ macro into it for debugging
 */
void my_checkheap(const char* func, int lineno) {
// Print original caller
#define ch_printf(FORMAT, ...) \
  dbg_printf("%s(%d): " FORMAT, func, lineno, ##__VA_ARGS__)
  void* bp;
  void* header;
  void* footer;
  void* heap_end = (char*)mem_heap_hi() + 1;
  void* prev;
  if ((heap - DSIZE - (char*)(mem_heap_lo())) !=
      LIST_SIZE * DSIZE) {
    ch_printf("Seglist pointers don't have enough space.");
  }
  // Prologue checking
  bp = heap;
  header = HDRP(bp);
  footer = FTRP(bp);
  if (GET_SIZE(header) != DSIZE || GET_ALLOC(header) != 1) {
    ch_printf("Prologue block smashed: wrong size (header)");
    ch_printf("Prologue header: " PACK_FMT, PACK_ARG(header));
    exit(EXIT_FAILURE);
  }
  if (GET_SIZE(footer) != DSIZE || GET_ALLOC(footer) != 1) {
    ch_printf("Prologue block smashed: wrong size (footer)");
    ch_printf("Prologue footer: " PACK_FMT, PACK_ARG(footer));
    exit(EXIT_FAILURE);
  }
  // Epilogue checking
  bp = heap_end;
  header = HDRP(bp);
  footer = FTRP(bp);
  if (GET_SIZE(header) != 0 || GET_ALLOC(header) != 1) {
    ch_printf("Epilogue block smashed: wrong size");
    ch_printf("Epilogue header: " PACK_FMT, PACK_ARG(header));
    exit(EXIT_FAILURE);
  }
  // Alignment checking
  for (bp = heap; bp != heap_end; bp = NEXT_BLKP(bp)) {
    if (!in_heap(bp)) {
      ch_printf("Block %p not in heap (%p:%p): ", bp, mem_heap_hi(),
                mem_heap_lo());
      ch_printf("Header: " PACK_FMT, PACK_ARG(HDRP(bp)));
      exit(EXIT_FAILURE);
    }
    if (!aligned(bp)) {
      ch_printf("Block %p not aligned", bp);
      ch_printf("Header: " PACK_FMT, PACK_ARG(HDRP(bp)));
      exit(EXIT_FAILURE);
    }
  }
  // H/F checking
  prev = heap;
  for (bp = NEXT_BLKP(heap); bp != heap_end;
       prev = bp, bp = NEXT_BLKP(bp)) {
    header = HDRP(bp);
    if (!GET_ALLOC(header)) {
      // free block
      footer = FTRP(bp);
      if (GET_SIZE(header) != GET_SIZE(footer) ||
          GET_ALLOC(header) != GET_ALLOC(footer) ||
          GET_PREVALLOC(header) != GET_PREVALLOC(footer)) {
        ch_printf("Block %p H/F mismatch:", bp);
        ch_printf("Header: " PACK_FMT, PACK_ARG(header));
        ch_printf("Footer: " PACK_FMT, PACK_ARG(footer));
        exit(EXIT_FAILURE);
      }
    }
    if (GET_SIZE(header) < 2*DSIZE) {
      ch_printf("Block %p too small: ", bp);
      ch_printf("Header: " PACK_FMT, PACK_ARG(header));
      exit(EXIT_FAILURE);
    }
    if (!!GET_PREVALLOC(header) != GET_ALLOC(HDRP(prev))) {
      ch_printf("BTAG of block %p doesn't match previous block ALLOC:", bp);
      ch_printf("Current(%p) header: " PACK_FMT, bp, PACK_ARG(HDRP(bp)));
      ch_printf("Previous(%p) header: " PACK_FMT, prev,
                PACK_ARG(HDRP(prev)));
      exit(EXIT_FAILURE);
    }
  }
  // Coalescing checking
  prev = heap;
  for (bp = NEXT_BLKP(heap); bp != heap_end;
       prev = bp, bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(prev)) && !GET_ALLOC(HDRP(bp))) {
      ch_printf("Adjacent free block %p and %p", prev, bp);
      ch_printf("%p header: " PACK_FMT, prev, PACK_ARG(HDRP(prev)));
      ch_printf("%p header: " PACK_FMT, bp, PACK_ARG(HDRP(prev)));
      exit(EXIT_FAILURE);
    }
  }
  // Seglist checking
  for (int i = 0; i < LIST_SIZE; i++) {
    bp = segregated_list[i];
    if (bp && !in_heap(bp)) {
      ch_printf("segregated_list[%d] (%p) head not in heap.", i, bp);
      exit(EXIT_FAILURE);
    }
  }
  for (bp = heap; bp != heap_end; bp = NEXT_BLKP(bp)) {
    if (!GET_ALLOC(HDRP(bp))) {
      if (GET_NEXT_FREE(bp) && !in_heap(GET_NEXT_FREE(bp))) {
        ch_printf("Free block %p 's next (%p) is not in heap.", bp,
                  GET_NEXT_FREE(bp));
        exit(EXIT_FAILURE);
      }
      if (GET_PREV_FREE(bp) && !in_heap(GET_PREV_FREE(bp))) {
        ch_printf("Free block %p 's prev (%p) is not in heap.", bp,
                  GET_PREV_FREE(bp));
        exit(EXIT_FAILURE);
      }
    }
  }
  for (int i = 0; i < LIST_SIZE; i++) {
    void* bp = segregated_list[i];
    while (bp) {
      bp = GET_NEXT_FREE(bp);
      if (bp && GET_NEXT_FREE(GET_PREV_FREE(bp)) != bp) {
        ch_printf("Mistaken linking between free blocks: ");
        ch_printf("bp            : %p", bp);
        ch_printf("bp->prev      : %p", GET_PREV_FREE(bp));
        ch_printf("bp->prev->next: %p", GET_NEXT_FREE(GET_PREV_FREE(bp)));
        exit(EXIT_FAILURE);
      }
    }
  }
#undef ch_printf
}

// End debug functions
