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

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본 상수 메크로 */
#define WSIZE       4                                                       /* header/footer 크기(bytes) */
#define DSIZE       8                                                       /* Double world 크기(bytes) */
#define CHUNKSIZE   (1<<12)                                                 /* Extend heap by this amount(bytes) */

#define MAX(x, y)   ((x) > (y) ? (x) : (y))                                 /* 두 값중 큰 값 구하기 */

#define PACK(size, alloc)   ((size) | (alloc))                              /* 크기와 할당된 비트를 Pack */

#define GET(p)      (*(unsigned int *) (p))                                 /* p가 가리키는 값을 반환 */
#define PUT(p, val) (*(unsigned int *) (p) = (val))                         /* p에 값 setting */

#define GET_SIZE(p)     (GET(p) & ~0x7)                                     /* 블록의 크기 반환 */
#define GET_ALLOC(p)    (GET(p) & 0x1)                                      /* 할당 여부 판단 */

#define HDRP(bp)    ((char *)(bp) - WSIZE)                                  /* header의 시작 위치 */
#define FTRP(bp)    ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)             /* footer의 시작 위치 */

#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))   /* 다음 블록의 playload 시작 위치 */
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))   /* 이전 블록의 playload 시작 위치 */

static void *extend_heap(size_t words);         /* 새 가용 블록으로 힙 확장 */
static void *coalesce(void *ptr);               /* 인접 가용 블록들과 통합 */
// static void *find_fit(size_t asize);            /* 가용 리스트를 처음부터 검색해서 크기가 맞는 첫 번째 가용 블록을 선택 */
static void *next_fit(size_t asize);            /* 마지막으로 찾은 가용 리스트 부터 검색하고 못찾으면 처음부터 검색 */
static void place(void *ptr, size_t asize);     /* 가용 공간과 할당할 사이즈가 들어갈 수 있는 공간에 header와 footer에 정보를 
                                                넣어주고 공간 할당을 하고 남은 부분이 있으면 
                                                (넣어줄 가용 블록 크기 - 할당할 크기)만큼을 가용공간으로 만듬 */

static char *last_listp = NULL;                 /* next_fit에서 가용하기 위한 정적 전역 변수 */
static char *heap_listp = NULL;                 /* find_fit에서 사용하기 위한 정적 전역 변수 */

/* 
 * mm_init - malloc 초기화.
 */
int mm_init(void)
{
    /* 최소 16바이트(header, footer, playlog)을 할당해야되는데 전체로 봤을 때 16바이트를 할당할 수 없으면 return -1 */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) {
        return -1;
    }
    PUT(heap_listp, 0);                             /* Alignment 패딩, Epilogue의 헤더는 4바이트이므로 8바이트를 맞추기 위해 맨 앞에 4바이트에 0으로 패딩 */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue 헤더 */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue 푸터 */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue 헤더 */
    heap_listp += (2*WSIZE);                        /* heap_listp위치를 footer의 위치로 이동, find_fit에서 처음 위치를 가리키는 용도로 사용 */
    last_listp = heap_listp;

    /* CHUNKSIZE: (1<<12) = 4096, 초기에 가용블록으로 힙을 확장 시도, 만약에 4096바이트를 확장 시켜줄 공간이 없다면 return -1, 있다면 공간 확장*/
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
* extend_heap - 새 가용 블록으로 힙을 확장
*/
static void *extend_heap(size_t words) {
    char *ptr;
    size_t size;

    /* 64bit 운영체제는 주소 단위를 8바이트로 읽기 때문에 최소 8바이트가 필요 */
    /* words은 어떠한 값에서 4로 나눈 몫을 가지고 옴 */
    /* 짝수 * 4는 무조건 8의 배수이기 때문에 홀수일 때 짝수로 만들어서 *4를 함 */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    /* 늘릴 수 있는 공간이 있으면 늘려 주고 늘릴 수 없을 때 return NULL 늘릴 수 있을 때는 늘려줌 */
    if ((ptr = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }

    /* 현재 포인터의 header와 footer에 size와 가용블록이라고 체크 */
    /* footer뒤에 epilogue 설정 */
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1));
    
    /* 새 가용 블록으로 힙을 확장하고 이전 블록이 가용블록이면 합침 */
    return coalesce(ptr);
}

/* 
 * mm_malloc - brk포인터를 증가시킴으로써 블록을 할당
 *     8바이트로 정렬된 포인터를 할당
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* 할당하고 싶은 사이즈를 8의 배수 형태로 변환한 것을 담을 변수 */
    size_t extendsize;  /* 할당하고 싶은 사이즈를 담을 공간이 없을 경우 공간 확장해줄 사이즈를 담을 변수 */
    char *ptr;          /* 할당할 포인터를 담을 변수 */

    /* 할당할 사이즈가 0이면 NULL 반환 */
    if (size == 0) {
        return NULL;
    }

    /* 할당할 크기가 8바이트보다 작으면 asize에 16바이트를 담음 */
    /* 할당할 크기가 8바이트보다 크면 8의 배수로 맞춰줘야되기 때문에
    (header/footer의 크기 8바이트 + 7바이트 + 할당할 크기) / 8을 하면 
    나머지는 버려지고 몫만 남는데 그 몫 * 8을 하면 할당할 크기를 담을 수 있는
    최소한의 크기의 8의 배수를 구할 수 있음 */
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    /* ptr = 할당하고 싶은 크기를 담을 수 있는 포인터, ptr이 NULL 아니면 place에서 공간을 잘라줌 */
    if ((ptr =  next_fit(asize)) != NULL) {
        place(ptr, asize);
        return ptr;
    }

    /* asize와 CHUNKSIZE중 큰 값을 가지고 새 가용 블록으로 힙을 확장 */
    /* ptr = 확장된 힙의 시작 포인터 */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((ptr = extend_heap(extendsize / WSIZE)) == NULL) {
        return NULL;
    }
    /* place에서 할당하고 싶은 크기로 공간을 잘라줌 */
    place(ptr, asize);
    return ptr;
}

/*
* find_fit - 가용 리스트를 처음부터 검색해서 크기가 맞는 첫 번째 가용 블록을 선택
*/
// static void *find_fit(size_t asize) {
//     void *ptr;
    
//     /* ptr = heap_listp(즉, init에서 설정했던 Prologue); 
//     조건은 블록의 크기가 0보다 클 때(즉, Epilogue를 만날 때 까지)반복
//     실행이 끝나면 ptr = 다음 블록의 payload 시작 위치 */
//     for(ptr = heap_listp; GET_SIZE(HDRP(ptr)) > 0; ptr = NEXT_BLKP(ptr)) {
//         /* 현재 블록이 가용 블록이고, 할당하고 싶은 사이즈 보다 현재 블록이 더 클 때 포인터 반환 */
//         if(!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))) {
//             return ptr;
//         }
//     }
//     /* 알맞는 크기를 못찾았을 때 NULL 반환 */
//     return NULL;
// }

static void *next_fit(size_t asize) {
    void *ptr;

    for(ptr = last_listp; GET_SIZE(HDRP(ptr)) != 0; ptr = NEXT_BLKP(ptr)) {
        /* 현재 블록이 가용 블록이고, 할당하고 싶은 사이즈 보다 현재 블록이 더 클 때 포인터 반환 */
        if(!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))) {
            last_listp = ptr;
            return ptr;
        }
    }
    /* 마지막으로 찾은 위치 다음부터 못찾았을 때 처음 부터 탐색 */
    for (ptr = heap_listp; (char *)ptr < last_listp; ptr = NEXT_BLKP(ptr)) {
        if (!GET_ALLOC(HDRP(ptr)) && GET_SIZE(HDRP(ptr)) >= asize) {
            last_listp = ptr;
            return ptr;
        }
    }
    return NULL;
}

/*
* place - 할당할 크기를 담을 수 있는 블록을 분할 해줌
*   할당할 크기를 담을 수 있는 블록 - 할당할 블록이 16바이트보다 크면
*   나중에 16바이트 크기만큼 할당하고 싶을 때 사용할 수 있기 때문에
*   분할 해서 뒤에 공간은 가용 공간으로 만들어줌
*   내부 단편화를 줄여줌       
*/
static void place(void *ptr, size_t asize) {
    size_t csize = GET_SIZE(HDRP(ptr));         /* 현재 블록의 크기 */

    /* 만약 할당할 크기를 담을 수 있는 블록 - 할당할 블록이 16바이트보다 크면 */
    /* 앞의 공간은 할당하고 남은 공간은 가용 블록으로 만들어 줌*/
    /* 아니면 */
    /* 할당할 크기만큼 할당 */
    if((csize - asize) >= (2*DSIZE)) {
        PUT(HDRP(ptr), PACK(asize, 1));
        PUT(FTRP(ptr), PACK(asize, 1));
        ptr = NEXT_BLKP(ptr);
        PUT(HDRP(ptr), PACK(csize - asize, 0));
        PUT(FTRP(ptr), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
    }
}

/*
 * mm_free - 공간 할당 해제
 */
void mm_free(void *ptr)
{   
    size_t size = GET_SIZE(HDRP(ptr));  /* 현제 블록의 크기 */

    /* header와 footer를 가용 블록으로 만들어 주고 이전 블록과 다음 블록을 체크해서 공간을 합쳐줌 */
    PUT(HDRP(ptr), PACK(size, 0));   
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/*
* coalesce - 인접 가용 블록들과 통합
*/
static void *coalesce(void *ptr) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));    /* 이전 블록이 가용상태인지 확인 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));    /* 다음 블록이 가용상태인지 확인 */
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && !next_alloc) {                                                /* 다음 블록이 가용상태이고 이전 블록이 가용 상태가 아니라면 */
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));                                         /* 다음 블록의 크기를 size에 더해줌 */
        PUT(HDRP(ptr), PACK(size, 0));                                                  /* 현재 header에 size를 넣고 가용상태로 만들어줌 */
        PUT(FTRP(ptr), PACK(size, 0));                                                  /* FTRP는 bp + 현재 header의 크기 - 8을 한 곳(즉, 다음 블록의 footer)에 size를 넣고 가용상태로 만들어줌 */ 
    } else if (!prev_alloc && next_alloc) {                                         /* 이전 블록이 가용상태이고 다음 블록이 가용 상태가 아니라면 */
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));                                         /* 이전 블록의 크기를 size에 더해줌 */
        PUT(FTRP(ptr), PACK(size, 0));                                                  /* 현재 footer에 size를 넣고 가용상태로 만들어줌 */
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));                                       /* 이전 블록의 header에 size를 넣고 가용상태로 만들어줌 */
        ptr = PREV_BLKP(ptr);                                                           /* 이전 블록의 payload 시작 위치를 ptr에 담음 */
    } else if (!prev_alloc && !next_alloc) {                                        /* 이전 블록과 다음 블록이 둘다 사용 상태일 때 */
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(FTRP(NEXT_BLKP(ptr)));        /* 이전 블록과 다음블록의 크기를 size에 더해줌*/
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));                                       /* 이전 블록의 header에 size를 넣어줌 */
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));                                       /* 다음 블록의 footer에 size를 넣어줌 */
        ptr = PREV_BLKP(ptr);                                                           /* 이전 블록의 payload 시작 위치를 ptr에 담음 */
    }
    if (HDRP(ptr) < last_listp && FTRP(ptr) > last_listp){
        last_listp = ptr;                                                          /* 마지막으로 찾은 위치 last_listp를 ptr로 바꿈 */
    }
    return ptr;                                                                     /* ptr 반환 */
}

/*
 * mm_realloc - 공간 재할당
 */
void *mm_realloc(void *bp, size_t size)
{
    /* size가 0과 같거나 작으면 공간을 free 해주고 return */
    if (size <= 0)
    {
        mm_free(bp);
        return 0;
    }
    /* bp가 NULL이면 새로 size만큼 크기 할당 */
    if (bp == NULL)
    {
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);   /* size만큼 새로운 공간 할당 */
    if (newp == NULL)   /* 메모리가 MAX_HEAP을 초과할 때 */
    {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));    /* 현재 크기를 oldsize에 담음 */
    if (size < oldsize)
    {
        oldsize = size; /* size가 oldsize보다 작으면 oldsize를 변경 */
    }
    memcpy(newp, bp, oldsize);  /* 복사받을 메모리를 가리키는 포인터, 복사할 메모리를 가리키는 포인터, 길이 */
    mm_free(bp);                /* 기존의 메모리 free */
    return newp;
}