/* Author: Tarang Patel      Email: 201101110@daiict.ac.in      ID: 201101110 */


/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this approach, the outline of the block is such that, payload 
 * is used to store prev and next pointers of the prev and next free block,
 * if the block is free. There are macros defined which compute the address
 * of previous and next free block, only if the blocks are free.
 * Then, a explicit free list is maintained in which the block pointer is added  if the block is free and is removed if it gets allocated. 
 *Two functions, insert_free_list and delete_free_list are defined to maintain the explicit free list
 */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>
#include "mm.h"
#include "memlib.h"


team_t team = {
    /* Team name */
    "Tarang Patel",
    /* First member's full name */
    "Tarang Patel",
    /* First member's email address */
    "201101110@daiict.ac.in",
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

#define PREV_FREE_BLKP(ptr) (*(void **) (ptr))                              /* ptr의 prev */
#define NEXT_FREE_BLKP(ptr) (*(void **) (ptr + WSIZE))                      /* ptr의 next */

#define SET_PREV_FREE(bp, prev) (*((void **)(bp)) = prev)                   /* ptr의 prev에 값 세팅 */
#define SET_NEXT_FREE(bp, next) (*((void **)(bp + WSIZE)) = next)           /* ptr의 next에 값 세팅 */

static char *free_list_head;                /* next_fit에서 가용하기 위한 정적 전역 변수 */
static char *heap_listp;                    /* find_fit에서 사용하기 위한 정적 전역 변수 */

static void *extend_heap(size_t words);         /* 새 가용 블록으로 힙 확장 */
static void *coalesce(void *ptr);               /* 인접 가용 블록들과 통합 */
static void *find_fit(size_t asize);            /* 가용 리스트를 처음부터 검색해서 크기가 맞는 첫 번째 가용 블록을 선택 */
static void place(void *ptr, size_t asize);     /* 가용 공간과 할당할 사이즈가 들어갈 수 있는 공간에 header와 footer에 정보를 
                                                넣어주고 공간 할당을 하고 남은 부분이 있으면 
                                                (넣어줄 가용 블록 크기 - 할당할 크기)만큼을 가용공간으로 만듬 */

static void delete_list(void *ptr);             /* 가용 블록 리스트에서 삭제 */
static void insert_list(void *ptr);             /* 가용 블록 리스트에 연결(주소순) */

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
    heap_listp += DSIZE;                        /* heap_listp위치를 footer의 위치로 이동, find_fit에서 처음 위치를 가리키는 용도로 사용 */
    free_list_head = NULL;
    /* CHUNKSIZE: (1<<12) = 4096, 초기에 가용블록으로 힙을 확장 시도, 만약에 4096바이트를 확장 시켜줄 공간이 없다면 return -1, 있다면 공간 확장*/
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
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
    (header/footer의 크기 8바이트) + size + 7 & ~0x07 */
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    } else {
        asize = ALIGN((size + DSIZE));
    }

    /* ptr = 할당하고 싶은 크기를 담을 수 있는 포인터, ptr이 NULL 아니면 place에서 공간을 잘라줌 */
    if ((ptr =  find_fit(asize)) != NULL) {
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
* extend_heap - 새 가용 블록으로 힙을 확장
*/
static void *extend_heap(size_t words) {
    char *ptr;
    size_t size;

    /* 64bit 운영체제는 주소 단위를 8바이트로 읽기 때문에 최소 8바이트가 필요 */
    /* words은 어떠한 값에서 4로 나눈 몫을 가지고 옴 */
    /* (몫 * 4) & ~0x07, 즉, 현재 사이즈를 담을 수 있는최소 8의 배수*/
    size = ALIGN(words * WSIZE);
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
* coalesce - 인접 가용 블록들과 통합
*/
static void *coalesce(void *ptr) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));    /* 이전 블록이 가용상태인지 확인 */
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));    /* 다음 블록이 가용상태인지 확인 */
    size_t size = GET_SIZE(HDRP(ptr));                      /* 현재 블록 크기 */

    if (prev_alloc && next_alloc){                                                  /* 양쪽 다 가용 블록이 없을 때 */
        insert_list(ptr);                                                               /* 현재 블록을 가용 리스트에 연결 */
    }
    else if (prev_alloc && !next_alloc) {                                           /* 다음 블록이 가용상태이고 이전 블록이 가용 상태가 아니라면 */
        delete_list(NEXT_BLKP(ptr));                                                    /* 다음 블록 연결 해제 */
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));                                         /* 다음 블록의 크기를 size에 더해줌 */
        PUT(HDRP(ptr), PACK(size, 0));                                                  /* 현재 header에 size를 넣고 가용상태로 만들어줌 */
        PUT(FTRP(ptr), PACK(size, 0));                                                  /* FTRP는 bp + 현재 header의 크기 - 8을 한 곳(즉, 다음 블록의 footer)에 size를 넣고 가용상태로 만들어줌 */ 
        insert_list(ptr);                                                               /* 현재 블록을 가용 리스트에 연결 */
    } else if (!prev_alloc && next_alloc) {                                         /* 이전 블록이 가용상태이고 다음 블록이 가용 상태가 아니라면 이전 블록이 가용 상태이면 이미 가용 블록 리스트에 있기 때문에 delete, insert가 필요 없음*/
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));                                         /* 이전 블록의 크기를 size에 더해줌 */
        PUT(FTRP(ptr), PACK(size, 0));                                                  /* 현재 footer에 size를 넣고 가용상태로 만들어줌 */
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));                                       /* 이전 블록의 header에 size를 넣고 가용상태로 만들어줌 */
        ptr = PREV_BLKP(ptr);                                                           /* 이전 블록의 payload 시작 위치를 ptr에 담음 */
    } else if (!prev_alloc && !next_alloc) {                                        /* 이전 블록과 다음 블록이 둘다 가용 상태 일때, 합쳐지므로 다음 블록만 가용 블록 리스트에서 지워주면 됨 */
        delete_list(NEXT_BLKP(ptr));                                                    /* 다음 블록 연결 해제 */
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(FTRP(NEXT_BLKP(ptr)));        /* 이전 블록과 다음블록의 크기를 size에 더해줌*/
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));                                       /* 이전 블록의 header에 size를 넣어줌 */
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));                                       /* 다음 블록의 footer에 size를 넣어줌 */
        ptr = PREV_BLKP(ptr);                                                           /* 이전 블록의 payload 시작 위치를 ptr에 담음 */
    }
    return ptr;                                                                     /* ptr 반환 */
}

/*
* delete_list - 가용 블록 리스트에서 현재 블록 삭제
*/
static void delete_list(void *bp) {
    void *next = (void *) NEXT_FREE_BLKP(bp);   /* next = 현재 블록의 다음 가용 블록 */
    void *prev = (void *) PREV_FREE_BLKP(bp);   /* prev = 현재 블록의 이전 가용 블록 */
    
    /* prev가 NULL이면 free_list_head = 다음 블록 */
    /* NULL이 아니면 이전 가용 블록의 next를 현재 블록의 다음 가용 블록으로 세팅 */
    if (prev == NULL) {
        free_list_head = next;
    } else {
        SET_NEXT_FREE(prev, next);
    }
    
    /* 현재 블록의 다음 가용 블록이 NULL이 아니면 다음 가용 블록의 prev를 현재 가용 블록의 prev로 설정 */
    if (next != NULL) { 
        SET_PREV_FREE(next, prev);
    }
}

/*
*   insert_list - 가용 블록 리스트에 현재 블록 삽입
*/
static void insert_list(void *bp) {
    void *current = free_list_head;             
    void *temp = current;
    void *prev = NULL;

    /* current가 NULL아니거나 현재 블록 주소가 current보다 작을 때 까지 반복 */
    /* 즉, temp에는 현재 블록의 직후 가용 블록 */
    while (current != NULL && bp < current) {
        prev = PREV_FREE_BLKP(current);
        temp = current;
        current = NEXT_FREE_BLKP(current);
    }
    
    SET_PREV_FREE(bp, prev);    /* 현재 prev에 찾은 가용 블록의 prev를 세팅 */
    SET_NEXT_FREE(bp, temp);    /* 현재 next에 찾은 가용 블록을 세팅 */

    /* prev가 NULL이면 free_list_head = 다음 블록 */
    /* NULL이 아니면 이전 가용 블록의 next를 현재 블록의 다음 가용 블록으로 세팅 */
    if (prev != NULL) { 
        SET_NEXT_FREE(prev, bp);
    } else { 
        free_list_head = bp;
    }

    /* 현재 블록의 다음 가용 블록이 NULL이 아니면 다음 가용 블록의 prev를 현재 가용 블록의 prev로 설정 */
    if (temp != NULL) {
        SET_PREV_FREE(temp, bp);
    }
}


/*
* find_fit - 가용 리스트를 처음부터 검색해서 크기가 맞는 첫 번째 가용 블록을 선택
*/
static void *find_fit(size_t asize) {
   void *ptr;
   for(ptr = free_list_head; ptr != NULL; ptr = NEXT_FREE_BLKP(ptr)) {
      /* 할당하고 싶은 사이즈 보다 현재 블록이 더 클 때 포인터 반환 */
      if(asize <= GET_SIZE(HDRP(ptr))) {
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
    delete_list(ptr);
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
        insert_list(ptr);
    } else {
        PUT(HDRP(ptr), PACK(csize, 1));
        PUT(FTRP(ptr), PACK(csize, 1));
    }
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