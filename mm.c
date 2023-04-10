/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* $begin malloc macro */

/* 
If NEXT_FIT defined use next fit search, else use first fit search .
next_ptr pointer is used for next fit search
*/
#define NEXT_FITx

#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  
                                                                                                                                                                   
#define PACK(size, alloc)  ((size) | (alloc))   // size와 alloc(a)의 값을 한 word로 묶는다. 이를 이용해 header, footer에 쉽게 저장할 수 있다.

/* read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))     // argument p is usually (void*) pointer
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

#define GET_SIZE(p)   (GET(p) & ~0x7)       // "mask out". 최하위 3bit 제거한 값 리턴.
#define GET_ALLOC(p)  (GET(p) & 0x1)        // &: 비트연산자 AND. "mask with". 1&1 = 1, 0&1=0. 만약 block address가 0x9라면 1001 -> 0x1로 masked됨(0001). -> 1 & 1 = 1 / 0 & 1 = 0. 

/* compute address of its header and footer */
#define HDRP(bp)    ((char *)(bp) - WSIZE)
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp))-DSIZE)    // GET_SIZE는 header, footer 포함한 토탈 사이즈임. 더블워즈만큼 빼줘야 footer 주소. if header value is 0x8 (1000) -> GET ALLOC => mask 0 & 0 = 0.

/* 블록포인터(bp)로 이전 블록과 다음 블록의 주소를 계산. 
- header에 있는 size를 포인터에 더해서 다음 블록으로 나아갈 수 있는데
bp를 인자로 받았기 때문에 -WSIZE로 header pointer로 넘어간 후 사이즈를 읽는다. 
*/
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end malloc macro */


/* Global variables */
static char *heap_listp = 0;        // pointer to first block
#ifdef NEXT_FIT 
static char *next_ptr;             // Next fit next_ptr
# endif

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))


/* $begin function */
int mm_init(void); 
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
static void *find_fit(size_t asize);
static void *coalesce(void *bp); 
void mm_free(void *bp);
static void place(void *bp, size_t asize);
void *mm_realloc(void *ptr, size_t size);
/* $end function */



/* 
 * mm_init - initialize the malloc package.
 최초 가용 블록으로 힙 생성: heap_listp는 프롤로그, 에필로그 할당 이후 그 사이의 첫 시작을 가리키도록 함.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) // sbrk는 void 리턴
        return -1;
    PUT(heap_listp, 0);                             // alignment padding. This is used to ensure that the subsequent headers and footers are aligned on a double-word boundary.
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    // prologue header. 1 is marked as allocated.
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    // prologue footer 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        // epilogue header
    heap_listp += (2*WSIZE);                // prolog 이후 힙의 첫 시작을 가리키도록 함.

#ifdef NEXT_FIT
    next_ptr = heap_listp;
#endif

    /* extend heap with free bloc of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    // printf("init");
    return 0;
}   


static void *extend_heap(size_t words)   // 워즈 개수를 parameter로.
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)      // void를 long으로 typecase한 것은, 정수형 -1과 비교하기 위해. sbrk() 함수가 새로 할당된 블록의 시작 주소 또는 -1을 리턴하는데. if는 integer -1과 비교하기 때문에, -1과 비교되려면 integer 타입으로 변환되어야. C에서 void*는 다양한 사이즈가 올 수 있기에 conversion이 무난히 될 수 있는(small->big은 가능), 가장 큰 사이즈 long을 부여.
        return NULL;    // allocate fail이면 NULL 리턴
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));       // Free block header, 그 값에 할당할 size를 넣음.
    PUT(FTRP(bp), PACK(size, 0));       // Free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue header

    /* Coalesce if the previous block was free */
    // printf("extend_heap");
    return coalesce(bp);
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
- malloc 함수는 size 바이트의 메모리 블록을 요청. 
    요청한 블록 크기를 조절해서 header, footer를 위한 공간을 확보하고, 더블워즈 요건을 만족.
    최소 16바이트 크기 블록으로 구성할 수 있도록 함. (8바이트는 정렬요건, 추가 8바이트는 헤더/풋터 오버헤드를 위해)
- 8바이트를 넘는 요청에 대해선, 오버헤드 바이트 내에 더해주고- 인접 8배수로 반올림
-  
 */
void *mm_malloc(size_t size)
{
    size_t asize;           // Adjusted block size
    size_t extendsize;      // Amount to extend heap if not fit
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;        // 오버헤드 포함 16바이트
    else                        // 8바이트 넘는 요청
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);  
        // 여기서 (DSIZE-1)은 엄밀히 말하면 (DSIZE - (size % DSIZE)) % DSIZE / ex) if size=20, padding is 4

    /* 적절한 가용블록을 가용리스트에서 검색, bp로 선언 */
    if ((bp = find_fit(asize)) != NULL){
        place(bp, asize);   // 맞는 블록을 찾으면 요청한 블록을 배치, 옵션으로 초과부분을 분할. 
        return bp;
    }
    // No fit found. Get more memory and place the block
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);       // extend_heap에 성공하면 
    // printf("malloc");
    return bp; 
}

/* First fit 사용
- 리스트 첫 부분부터 검색하면서 해당 size 블록 찾는 방법
- 반복문. 
*/
static void *find_fit(size_t asize)
{
#ifdef NEXT_FIT
    /* Next fit search */
    char *bp = next_ptr;

    /* next_ptr에서 리스트 끝까지 검색. epilogue(0) 전까지 */
    for ( ; GET_SIZE(HDRP(next_ptr)) > 0; next_ptr = NEXT_BLKP(next_ptr))
        if (!GET_ALLOC(HDRP(next_ptr)) && (asize <= GET_SIZE(HDRP(next_ptr))))
            return next_ptr;
    
    /* 리스트 시작에서 이전 next_ptr까지 검색 */
    for (next_ptr = heap_listp; next_ptr < bp; next_ptr = NEXT_BLKP(next_ptr)){
        if (!GET_ALLOC(HDRP(next_ptr)) && (asize <= GET_SIZE(HDRP(next_ptr))))
            return next_ptr;
    }
    return NULL;

#else
    /* First fit search */
    void *bp;       // 왜 void?

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){  
        // 블록사이즈가 1 WORD 이상이면 if문 실행. 그렇지 않으면 다음블록으로
        // 현재 bp 블록이 free이고 요청사이즈보다 클 때 리턴 
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
            // printf("find_fit");
            return bp;
        }
    }
    return NULL;   

#endif
}



/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));      // 헤더에 있는 payload size 리턴

    PUT(HDRP(bp), PACK(size, 0));          // size, 0을 한 word로 PACK 해서 HDRP 값으로 저장.
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));         // 0 or 1
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));            // 현재 블록 사이즈

    if (prev_alloc && next_alloc){              // 1, 1
        return bp;
    }

    else if (prev_alloc && !next_alloc){        // 1, 0
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));           // 늘어난 size만큼 기록. 
        PUT(FTRP(bp), PACK(size, 0)); 
        // bp 헤더는 그대로임.
    }

    else if (!prev_alloc && next_alloc){            // 0, 1
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      // 이전 bp 헤더에 있는 pure size를 읽어라
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 현재 bp의 header란 없음. 이전 bp의 헤더에 기록
        // 이전 블록과 병합한 뒤 새로운 bp return
        bp = PREV_BLKP(bp);     
    }

    else{           // prev, next 모두 0
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        // 이전, 다음 블록과 병합 뒤 새로운 bp return
        bp = PREV_BLKP(bp);
    }
#ifdef NEXT_FIT
    /* Make sure the next_ptr isn't pointing into the free block that we just coalesced */
    if ((next_ptr > (char *)bp) && (next_ptr < NEXT_BLKP(bp)))
        next_ptr = bp;
#endif
    // printf("coalesce");
    return bp;
}

/* place
- 블록을 배치한 후 나머지 부분의 크기가 최소블록 크기와 같거나 크다면, 블록을 분할해야.
- 다음 블록으로 이동하기 전 새로 할당한 블록 배치.
*/
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        // printf("place, splitted");
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        // printf("place, not splitted");
    }
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr));
    
    if (size < copySize)
      copySize = size;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    // printf("realloc");
    return newptr;
}














