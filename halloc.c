#include <assert.h>
#include <errno.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

// TODO: replace malloc by using this as a shared library (link time in CSAPP).
#ifndef USE_STD
#define malloc halloc
#define realloc hrealloc
#define calloc zalloc
#define free hfree
#endif

/* Choosing system page size to extend the heap with sbrk */
#define PAGE_SIZE 4096

/* 2 words for current and previous block info */
#define HEADER_SIZE (2 * sizeof(size_t))

/* 2 words for header and at least 2 for payload */
#define MIN_BLOCK_SIZE (4 * sizeof(size_t))
/* Blocks should end on double word boundary */
#define PAYLOAD_ALIGNMENT (2 * sizeof(size_t))

#define ROUND_UP(sz, align) (((sz) + (align) - 1) & -(align))

#define SIZE_MASK ~0x7
#define USED_MASK 0x1

#define PUT_CUR_INFO(hdr, sz, used) ((hdr)->cur_info = (sz) | (used))
#define PUT_CUR_USED(hdr, used)                                                \
  ((hdr)->cur_info = ((hdr)->cur_info & ~USED_MASK) | (used))
#define PUT_PREV_INFO(hdr, sz, used) ((hdr)->prev_info = (sz) | (used))

#define GET_CUR_SIZE(hdr) ((hdr)->cur_info & SIZE_MASK)
#define GET_PREV_SIZE(hdr) ((hdr)->prev_info & SIZE_MASK)
#define GET_CUR_USED(hdr) ((hdr)->cur_info & USED_MASK)
#define GET_PREV_USED(hdr) ((hdr)->prev_info & USED_MASK)

#define PUT_NEXT_FREE(hdr, nxt) ((hdr)->next_free = (nxt))
#define PUT_PREV_FREE(hdr, prev) ((hdr)->prev_free = (prev))
#define GET_NEXT_FREE(hdr) ((hdr)->next_free)
#define GET_PREV_FREE(hdr) ((hdr)->prev_free)

#define GET_NEXT_ADJ(hdr)                                                      \
  ((header_t *)((char *)(hdr) + GET_CUR_SIZE(hdr) + HEADER_SIZE))
#define GET_PREV_ADJ(hdr)                                                      \
  ((header_t *)((char *)(hdr) - GET_PREV_SIZE(hdr) - HEADER_SIZE))

/* Sentinel block has a size of zero and `used` bit is set to one. */
#define IS_SENTINEL(hdr) (!GET_CUR_SIZE(hdr) && GET_CUR_USED(hdr))

/* Goes from (header_t *) to (void *). */
#define HDR_TO_PAYLOAD_PTR(ptr) ((void *)((char *)(ptr) + HEADER_SIZE))

/* Goes from (void *) to (header_t *) */
#define PAYLOAD_TO_HDR_PTR(ptr) ((header_t *)((char *)(ptr) - HEADER_SIZE))

typedef struct header_t {
  size_t cur_info;
  size_t prev_info;
  struct header_t *next_free;
  struct header_t *prev_free;
} header_t;

static header_t *free_list = NULL;

static header_t *free_list_find(size_t size) {
  header_t *blk = free_list;

  while (blk) {
    if (GET_CUR_SIZE(blk) >= size) {
      return blk;
    }
    blk = blk->next_free;
  }

  return NULL;
}

/*
 * free_list_add only works with next_free & prev_free pointers.
 * cur_info & prev_info are information about adjacent blocks and
 * must be adjusted by the caller of this function.
 */
static void free_list_add(header_t *hdr) {
  PUT_NEXT_FREE(hdr, free_list);
  PUT_PREV_FREE(hdr, NULL);

  if (free_list) {
    PUT_PREV_FREE(free_list, hdr);
  }

  free_list = hdr;
}

static void free_list_remove(header_t *hdr) {
  if (hdr == free_list) {
    free_list = GET_NEXT_FREE(hdr);
  }
  header_t *next = GET_NEXT_FREE(hdr);
  header_t *prev = GET_PREV_FREE(hdr);
  if (prev) {
    PUT_NEXT_FREE(prev, next);
  }
  if (next) {
    PUT_PREV_FREE(next, prev);
  }
}

/*
 * Gets the header of a block to split and returns the second split.
 * Rounds up the size to a multiple of block alignment and updates
 * the size of hdr and retains its used bit. The split only happens if
 * the second split is larger (>=) than the min block size, in which case
 * it will be added to the free list. It will return hdr when split doesn't
 * happen.
 */
static header_t *free_list_split(header_t *hdr, size_t size) {
  /*
   * Round up the size to a multiple of payload size so that the blocks will
   * end on the double word boundary. This will cause internal fragmentation
   * in some cases e.g. when size is 17, aligned size becomes 32.
   */
  size_t align_size = ROUND_UP(size, PAYLOAD_ALIGNMENT);
  size_t rem = GET_CUR_SIZE(hdr) - align_size;
  if (rem < MIN_BLOCK_SIZE)
    return hdr;

  /* Retain `used` but update `size` */
  PUT_CUR_INFO(hdr, align_size, GET_CUR_USED(hdr));

  header_t *split2 = (header_t *)((char *)hdr + HEADER_SIZE + align_size);
  size_t split2_sz = rem - HEADER_SIZE;
  PUT_CUR_INFO(split2, split2_sz, 0);
  PUT_PREV_INFO(split2, align_size, GET_CUR_USED(hdr));
  free_list_add(split2);

  return split2;
}

/*
 * Returns `(header_t *)-1` in case of error.
 * The returned block will have its used bit set to 1.
 */
header_t *heap_extend(size_t size) {
  /*
   * We will use the previous sentinel block as header for this new
   * allocated block, but still we need header space at end of block
   * for the new sentinel block.
   */
  size_t align_size = ROUND_UP(size + HEADER_SIZE, PAGE_SIZE);

  void *oldbrk;
  if ((oldbrk = sbrk(align_size)) == (void *)-1) {
    return (header_t *)-1;
  }

  /*
   * blk happens to be the old sentinel block, but we will repurpose
   * that to be the header for the new block. prev_info is already
   * valid so we only need to change cur_info.
   */
  header_t *blk = (header_t *)((char *)oldbrk - HEADER_SIZE);
  PUT_CUR_INFO(blk, align_size - HEADER_SIZE, 1);

  header_t *sntl = (header_t *)((char *)blk + align_size);
  PUT_CUR_INFO(sntl, 0, 1);

  // TODO: free_list_coalesce_prev(blk);
  header_t *spltblk = free_list_split(blk, size);
  PUT_PREV_INFO(sntl, GET_CUR_SIZE(spltblk), 0);

  return blk;
}

void init() {
  void *block;
  if ((block = sbrk(PAGE_SIZE)) == (void *)-1) {
    fprintf(stderr, "Heap initialization failed: %s\n", strerror(errno));
    exit(1);
  }

  /* Without the following code, sbrk will misbehave. */
  FILE *devnull = fopen("/dev/null", "w");
  if (!devnull) {
    fprintf(stderr, "Failed to open /dev/null: %s\n", strerror(errno));
    exit(1);
  }
  fprintf(devnull, "sbrk return: (%p) as old brk\n", block);

  size_t page_size = sbrk(0) - block;

  /*
   * Subtracting the overhead of header of initial block and
   * the sentinel block
   */
  size_t size = page_size - 2 * HEADER_SIZE;
  header_t *hdr = (header_t *)block;
  PUT_CUR_INFO(hdr, size, 0);
  PUT_PREV_INFO(hdr, 0, 1);
  /*
   * Sentinel node is not part of the free list because it's not
   * a free block that can be allocated. We don't need it for boundary
   * checks either, because we can check if next_free is NULL.
   * It is useful, however, when walking through adjacent blocks using
   * size in header info, so we know where to stop.
   */
  header_t *sentinel = (header_t *)((char *)block + page_size - HEADER_SIZE);
  PUT_CUR_INFO(sentinel, 0, 1);
  PUT_PREV_INFO(sentinel, size, 0);

  /* Make sure ptrs to next and prev free block are null */
  PUT_NEXT_FREE(hdr, NULL);
  PUT_PREV_FREE(hdr, NULL);

  free_list = hdr;
}

void free_list_walk() {
  printf("Walking free blocks\n");
  header_t *block = free_list;
  while (block) {
    size_t sz = GET_CUR_SIZE(block);
    printf("Block (%p) size=%zu, used=%zu\n", block, sz, GET_CUR_USED(block));
    block = block->next_free;
  }
  printf("\n");
}

void heap_walk_adjacent(header_t *first) {
  printf("Walking adjacent blocks\n");
  header_t *block = first;
  while (1) {
    size_t sz = GET_CUR_SIZE(block);
    size_t used = GET_CUR_USED(block);
    if (sz == 0 && used == 1) {
      printf("Sentinel block (%p)\n", block);
      break;
    }
    printf("Block (%p) size=%zu, used=%zu\n", block, sz, used);
    block = (header_t *)((char *)block + HEADER_SIZE + sz);
  }
  printf("\n");
}

bool free_list_coalesce_next(header_t *blk) {
  /*
   * If we're here, we know that to_be_merged won't be NULL because coalesce
   * should not be called on the sentinel node.
   */
  header_t *to_be_merged = GET_NEXT_ADJ(blk);

  if (GET_CUR_USED(to_be_merged)) {
    return false;
  }

  /*
   * `new_size` is the combined size of `blk` and `to_be_merged` plus the
   * header space of `to_be_merged`.
   */
  size_t new_size =
      GET_CUR_SIZE(blk) + HEADER_SIZE + GET_CUR_SIZE(to_be_merged);

  free_list_remove(to_be_merged);
  PUT_CUR_INFO(blk, new_size, 0);

  /*
   * to_be_merged is not sentinel so there will be a block after it so it is
   * safe to deref new_next.
   */
  header_t *new_next = GET_NEXT_ADJ(to_be_merged);
  PUT_PREV_INFO(new_next, new_size, 0);

  return true;
}

header_t *free_list_coalesce_prev(header_t *blk) {
  /*
   * If previous block is used or blk is the first block of the heap.
   * prev_info on the first block of heap will have its used bit set to 1.
   */
  if (!GET_PREV_USED(blk)) {
    /* Because previous is free, coalesce will certainly happen. */
    blk = GET_PREV_ADJ(blk);
    free_list_coalesce_next(blk);
  }

  return blk;
}

/*
 * `coalesce` assumes hdr is a free block and only checks whether the
 * previous and next blocks are free.
 */
void free_list_coalesce(header_t *blk) {
  free_list_coalesce_next(blk);
  free_list_coalesce_prev(blk);
}

void hfree(void *blk) {
  header_t *hdr = PAYLOAD_TO_HDR_PTR(blk);

  size_t sz = GET_CUR_SIZE(hdr);
  PUT_CUR_INFO(hdr, sz, 0);
  PUT_PREV_INFO(GET_NEXT_ADJ(hdr), sz, 0);
  free_list_add(hdr);

  free_list_coalesce(hdr);
}

void *halloc(size_t size) {
  size_t align_size = ROUND_UP(size, PAYLOAD_ALIGNMENT);
  header_t *blk = free_list_find(align_size);
  if (blk) {
    /*
     * Try to split the block and add the second part to the free list.
     * We also need to mark the first split as used. Size of the block
     * could be different after the split, and free_list_split will take
     * care of that by updating the size and preserving the used bit.
     */
    free_list_remove(blk);
    PUT_CUR_USED(blk, 1);
    free_list_split(blk, align_size);
    return HDR_TO_PAYLOAD_PTR(blk);
  }

  if ((blk = heap_extend(align_size)) == (header_t *)-1) {
    return NULL;
  }

  return HDR_TO_PAYLOAD_PTR(blk);
}

void test_heap_extension();
void test_list_split();
void test_coalesce1();
void test_coalesce2();

int main() {
  init();
  header_t *firstblk = free_list;

  void *blk1 = malloc(10);
  void *blk2 = malloc(140000);

  void *blk3 = malloc(3000);
  void *blk4 = malloc(328);
  void *blk5 = malloc(1024);
  void *blk6 = malloc(1024);
  heap_walk_adjacent(firstblk);

  printf("freeing the first three blocks (%p)\n", blk4);
  free(blk1);
  free(blk5);
  free(blk4);
  heap_walk_adjacent(firstblk);

  printf("freeing the second 1024 (%p)\n", blk6);
  free(blk6);
  heap_walk_adjacent(firstblk);
}

/*          TESTS           */
/****************************/
void test_coalesce1() {
  init();
  header_t *firstblk = free_list;

  header_t *b16_1 = heap_extend(1);
  PUT_CUR_INFO(b16_1, GET_CUR_SIZE(b16_1), 0);
  free_list_add(b16_1);

  header_t *b16_2 = heap_extend(1);
  PUT_CUR_INFO(b16_2, GET_CUR_SIZE(b16_2), 0);
  free_list_add(b16_2);

  heap_walk_adjacent(firstblk);
  free_list_walk();
  printf("/******* COALESCE (%p) *******/\n", b16_1);
  free_list_coalesce(b16_1);

  heap_walk_adjacent(firstblk);
  free_list_walk();
}

void test_coalesce2() {
  init();
  header_t *firstblk = free_list;

  header_t *b16_1 = heap_extend(1);
  PUT_CUR_INFO(b16_1, GET_CUR_SIZE(b16_1), 0);
  free_list_add(b16_1);

  header_t *b16_2 = heap_extend(1);
  PUT_CUR_INFO(b16_2, GET_CUR_SIZE(b16_2), 0);
  free_list_add(b16_2);

  heap_walk_adjacent(firstblk);
  free_list_walk();
  printf("/******* COALESCE NEXT (%p) *******/\n", b16_2);
  assert(free_list_coalesce_next(b16_2));

  heap_walk_adjacent(firstblk);
  free_list_walk();
  printf("/******* COALESCE PREV (%p) *******/\n", b16_2);
  free_list_coalesce_prev(b16_2);
  heap_walk_adjacent(firstblk);
  free_list_walk();
}

void test_heap_extension() {
  init();

  header_t *firstblk = free_list;

  header_t *newblk;
  if ((newblk = heap_extend(10)) == (header_t *)-1) {
    fprintf(stderr, "Heap extension failed: %s\n", strerror(errno));
    exit(1);
  }
  printf("Heap Extension Block (%p) size=%zu, used=%zu\n", newblk,
         GET_CUR_SIZE(newblk), GET_CUR_USED(newblk));

  /* Walk adjacent */
  printf("Walking adjacent blocks\n");
  header_t *block = firstblk;
  while (1) {
    size_t sz = GET_CUR_SIZE(block);
    size_t used = GET_CUR_USED(block);
    if (sz == 0 && used == 1) {
      printf("Sentinel block (%p)\n", block);
      break;
    }
    printf("Block (%p) size=%zu, used=%zu\n", block, sz, used);
    block = (header_t *)((char *)block + HEADER_SIZE + sz);
  }

  free_list_walk();
}

void test_free_list_split() {
  header_t *hdr = (header_t *)malloc(96);
  PUT_CUR_INFO(hdr, 64, 0); /* 64/0 */
  free_list_add(hdr);

  header_t *sentinel = (header_t *)((char *)hdr + HEADER_SIZE + 64);
  PUT_CUR_INFO(sentinel, 0, 1);
  PUT_PREV_INFO(sentinel, 64, 0);

  header_t *split_block = free_list_split(hdr, 10);
  /* Walk adjacent */
  printf("Walking adjacent blocks\n");
  header_t *block = hdr;
  while (1) {
    size_t sz = GET_CUR_SIZE(block);
    size_t used = GET_CUR_USED(block);
    if (sz == 0 && used == 1) {
      printf("Sentinel block\n");
      break;
    }
    printf("Block (%p) size=%zu, used=%zu\n", block, sz, used);
    block = (header_t *)((char *)block + HEADER_SIZE + sz);
  }

  /* Walk free list */
  free_list_walk();

  free_list_remove(split_block);
  free_list_walk();

  free_list_remove(hdr);
  free_list_walk();

  free(hdr);
}
