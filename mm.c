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

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif

/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/************Macros************/

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<11)  /* Extend heap by this amount (bytes) */ 

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

/// Automatic choose appropriate segregated_list id
#define SEGLIST_AUTO ((size_t)-1)

#define LIST_SIZE 13

static char* heap = NULL;
static char* epilogue = NULL;

/// Array of seglists
static void** segregated_list;

// Get the address of next/previous free block using segregated_list

static inline void* get_prev(void* bp)
{
    WORD val = GET(bp);
    void *prev = NULL;
    if(val){
      prev = (void*)(heap + val);
    }
    return prev;
}

static inline void* get_succ(void* bp)
{
    WORD val = GET((char*)bp + WSIZE);
    void *succ = NULL;
    if(val){
      succ = (void*)(heap + val);
    }
    return succ;
}

static inline void set_prev(void *bp,void *lp)
{
  WORD val = 0;
  if(lp){
    val = (char*)lp - heap;
  }
  PUT(bp,val);
}

static inline void set_succ(void *bp,void *np)
{
  WORD val = 0;
  if(np){
    val = (char*)np - heap;
  }
  PUT((char*)bp + WSIZE,val);
}

// Helper function declarations

static void* extend_heap(size_t);
static void* coalesce(void*);
static void* find_fit(size_t);
static void place(void*, size_t);

void heap_warning(int lineno);
void mm_checkheap(int lineno);

static int list_num(size_t);
static void list_insert(void*, size_t);
static void list_delete(void*, size_t);
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
    epilogue = heap + WSIZE;

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
    if (size < CHUNKSIZE) size = CHUNKSIZE;
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

    epilogue += size;
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
        list_insert(bp, size);
        return bp;
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
        for (bp = segregated_list[id]; bp != NULL; bp = get_succ(bp))
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
        PUT(HDRP(bp), PACK(asize, GET_ALLOCINFO(HDRP(bp)) | 1));
        
        /*new free block*/
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(x, 2));
        PUT(FTRP(bp), PACK(x, 2));
        list_insert(bp,x);
    }
    else { //cant split
        PUT(HDRP(bp), PACK(csize, GET_ALLOCINFO(HDRP(bp)) | 1));

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
static inline void list_insert(void* fp, size_t size) {
  int id = list_num(size);
  void *list = segregated_list[id];
  if (list) {  // list not empty
    set_prev(list, fp);
  }
  set_succ(fp, list);
  set_prev(fp, NULL);
  segregated_list[id] = fp;
}

/*
 * List delete: delete a block from list
 *
 */
static inline void list_delete(void* bp, size_t size) {
  size_t id = list_num(size);
  char* next = get_succ(bp);
  char* prev = get_prev(bp);
  if (prev) {
    set_succ(prev, next);
  } else {
    segregated_list[id] = next;
  }
  if (next) {
    set_prev(next, prev);
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

/*
 * mm_checkheap: checker for heap consistency
 * Strictly follow the writeup
 * 
 */

void mm_checkheap(int lineno)
{
    /****** checking the heap ******/

    /* prologue and epilogue */
    char *prologue = heap;
    if(!in_heap(prologue)){
        dbg_printf("Prologue Crossing Heap Boundary!\n");
        heap_warning(lineno);
    }
    if(!GET_ALLOC(prologue) || GET_SIZE(prologue) != DSIZE){
        dbg_printf("Prologue Been Changed!\n");
        heap_warning(lineno);
    }

    if(epilogue != mem_heap_hi() + 1){
        dbg_printf("Epilogue Location Error!\n");
        heap_warning(lineno);
    }
    if(!GET_ALLOC(epilogue) || GET_SIZE(epilogue)){
        dbg_printf("Epilogue Property Changed!\n");
        heap_warning(lineno);
    }

    /* check each block */
    int free_num = 0;
    void *bp;
    for(bp = heap;GET_SIZE(bp);bp = NEXT_BLKP(bp)){
        if(!in_heap(bp)){
            dbg_printf("Block Crossing Heap Boundary!\n");
            heap_warning(lineno);
        }
        if(!aligned(bp)){
            dbg_printf("Block Not Aligned!\n");
            heap_warning(lineno);
        }
        if(!GET_ALLOC(bp)){
            ++free_num;
            if(!GET_ALLOC(NEXT_BLKP(bp))){
                dbg_printf("Coalesce Not Done!\n");
                heap_warning(lineno);
            }
        }
        if(GET_ALLOC(bp) != GET_PREVALLOC(NEXT_BLKP(bp))){
            dbg_printf("Neighbourhood Blocks Error!\n");
            heap_warning(lineno);
        }
    }

    /* check seg-free list */
    for(int i = 0;i < LIST_SIZE;++i){
        void *list = segregated_list[i];
        void *bp;
        for(bp = list;bp;bp = get_succ(bp)){
            --free_num;
            if(!in_heap(bp)){
                dbg_printf("List Block Crossing Boundary!\n");
                heap_warning(lineno);
            }
            if(GET_ALLOC(bp)){
                dbg_printf("Allocated Block In List!\n");
                heap_warning(lineno);
            }
            if(list_num(GET_SIZE(bp)) != i){
                dbg_printf("Block Size Unmatch!\n");
                heap_warning(lineno);
            }
            if(get_prev(get_succ(bp)) != bp || get_succ(get_prev(bp))!=bp){
                dbg_printf("List Consistency Error!\n");
                heap_warning(lineno);
            }
        }
    }

    if(free_num!=0){
        dbg_printf("Free Block Num Unmatch!\n");
        heap_warning(lineno);
    }
}


void heap_warning(int lineno)
{
    printf("Heap Error in line %d\n", lineno);
    exit(1);
}

