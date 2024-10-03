/*
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP3e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <math.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "Just Me",
    /* First member's full name */
    "Henry Pu",
    /* First member's NetID */
    "hyp2",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's NetID (leave blank if none) */
    ""};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (144)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(WSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


/* Global variables: */
static char *heap_listp; /* Pointer to first block */  

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static unsigned int calc_size(unsigned int n_bytes);
static void insert_block(void *bp, int size);
static void remove_block(void *bp);


/* Function prototypes for heap consistency checker routines: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* Struct that acts as a block of memory with next and previous pointers */
struct node
{
	char* next;
	char* prev;

}__attribute__((packed)); 


/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(19 * WSIZE)) == (void *)-1)
		return (-1);

	PUT(heap_listp, 0);                              /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(17 * WSIZE, 1));/* Prologue header */
	// Add the pointers for the free lists.
	for (int i = 2; i <= 16; i++) {
		PUT(heap_listp + (i * WSIZE), 0);  
	}
	PUT(heap_listp + (17 * WSIZE), PACK(17 * WSIZE, 1));/* Prologue footer*/ 
	PUT(heap_listp + (18 * WSIZE), PACK(0, 1));        /* Epilogue header */
	heap_listp += (2 * WSIZE);

	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if ((extend_heap(CHUNKSIZE / WSIZE)) == NULL)
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= DSIZE)
		asize = 2 * DSIZE;
	else
                //computet total amount of bytes needd
		asize = WSIZE * ((size + DSIZE + (WSIZE - 1)) / WSIZE);
	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		remove_block(bp);
		place(bp, asize);
		return (bp);
	}
	/* No fit found.  Get more memory and place the block. */
	if ((bp = extend_heap(MAX(asize, CHUNKSIZE) / WSIZE)) == NULL)  
		return (NULL);
	// Remove the block from the free list
	remove_block(bp);
	// Split the free size block to fit bp 
	place(bp, asize);
	return (bp);
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	// Insert block
	insert_block(bp, size);
	coalesce(bp);
	
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) {
        return mm_malloc(size);
    }

    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // Calculate header and old size upfront
    size_t oldsize = GET_SIZE(HDRP(ptr));
    void *header = HDRP(ptr); 

    // Calculate adjusted size and check for perfect fit
    size_t asize = WSIZE * ((size + DSIZE + (WSIZE - 1)) / WSIZE);
    if (asize == oldsize) {
        return ptr;
    }

    // Try coalescing with the next free block
    if (asize <= oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr))) && 
        !GET_ALLOC(HDRP(NEXT_BLKP(ptr)))) 
    {
        remove_block(NEXT_BLKP(ptr));
        PUT(header, PACK(oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0));
        PUT(FTRP(ptr), PACK(oldsize + GET_SIZE(HDRP(NEXT_BLKP(ptr))), 0)); 
        return ptr;
    }

    // Handle heap extension (combining similar logic)
    if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || GET_SIZE(HDRP(NEXT_BLKP(ptr))) == 0) {
        void *bp = mem_sbrk(asize - oldsize);
        if (bp == (void *)-1) {
            return NULL;
        }
        PUT(header, PACK(asize, 1)); 
        PUT(FTRP(ptr), PACK(asize, 1)); 
        PUT(HDRP(NEXT_BLKP(ptr)), PACK(0, 1)); 
        return ptr;
    }

    // Fallback: Allocate new block and copy
    void *newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }

    memcpy(newptr, ptr, size < oldsize ? size : oldsize);
    mm_free(ptr);
    return newptr;
}


/*
 * The following routines are internal helper routines.
 */
 /*
 * Requires:
 *   None
 * 
 * Effects:
 *   Gets the next block of memory.
*/
static void *
GET_NEXT(void *bp) 
{
    return ((struct node *)(bp))->next;
}

/*
 * Requires:
 *   "bp"-block of memory 
 *   "next"-block of memory to be set as the next of bp
 * 
 * Effects:
 *   Sets next block of bp to next
*/
static void
SET_NEXT(void *bp, void *next) 
{
    ((struct node *)(bp))->next = next;
}

/*
 * Requires:
 *   None
 * 
 * Effects:
 *   Gets previous block of memory.
*/
static void *
GET_PREV(void *bp) 
{
    return ((struct node *)(bp))->prev;
}

/*
 * Requires:
 *   "bp"-block of memory 
 *   "prev"-block of memory to be set as the previous of bp
 * 
 * Effects:
 *   Sets the previous block of memory of bp to prev.
*/
static void
SET_PREV(void *bp, void *prev) 
{
    ((struct node *)(bp))->prev = prev;
}

/*
 * Requires:
 *   unsigned int representing number of bytes
 * 
 * Effects:
 *   Computes and returns bucket size
*/
unsigned int 
calc_size(unsigned int bytes) {
	if (bytes <= 2) {
		return 0;
	}
	if (bytes <= 4) {
		return 1;
	}
	if (bytes <= 8) {
		return 2;
	}
	if (bytes <= 16) {
		return 3;
	}
	if (bytes <= 32) {
		return 4;
	}
	if (bytes <= 64) {
		return 5;
	}
	if (bytes <= 144) {
		return 6;
	}
	if (bytes <= 256) {
		return 7;
	}
	if (bytes <= 512) {
		return 8;
	}
	if (bytes <= 1024) {
		return 9;
	}
	if (bytes <= 2058) {
		return 10;
	}
	if (bytes <= 4096) {
		return 11;
	}
	if (bytes <= 8192) {
		return 12;
	}
	if (bytes <= 16384) {
		return 13;
	}
	/* Larger bytes */
	return 14; 	
}
/* 
 * Requires:
 *   "bp" is a block of memory we want to add to our free list.
 *   "size" is the size of the block of memory.
 *
 * Effects:
 *   Adds the block into our free list with the correct placement in the 
 *   segregated free lists.
 */
void
insert_block(void *bp, int size)
{
	// Find the range of sizes.
	int range = calc_size(size);
	char *list_head = heap_listp + (range * WSIZE);
	uintptr_t list_next = GET(list_head);
	// Set the next of the block.
	SET_NEXT(bp, (void*)list_next);
	// Set the previous of the block.
	SET_PREV(bp, list_head);
	// If the list is not empty, update the previous pointer of the next block.
	if (list_next != 0) {
		SET_PREV((void*)list_next, bp);
	}
	// Put the block into the list.
	PUT(list_head, (uintptr_t)bp);
}

/* 
 * Requires:
 *   "bp" block of memory 
 *
 * Effects:
 *   Removes block of memory from free list
 */
void
remove_block(void *bp)
{
	void *next_block = GET_NEXT(bp);
	void *prev_block = GET_PREV(bp);
	// If next block exists, set previous of next block.
	if (next_block != NULL) {
		SET_PREV(next_block, prev_block);
	}
	// If the block not at the beginning of list, update next of previous block.
	if (prev_block != NULL) {
		SET_NEXT(prev_block, next_block);
	}
}

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{
	size_t size = GET_SIZE(HDRP(bp));
	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
	// Case 1: If both prev and next exist, then just return the bp 
	if (prev_alloc && next_alloc) {                 
		return (bp);
	// Case 2: the curr block is used but the next block is free 
	} else if (prev_alloc && !next_alloc) {         
		// Remove blocks
		remove_block(NEXT_BLKP(bp)); 
		remove_block(bp); 
	// Add size of the next header by accessing header and add to curr size
		size += GET_SIZE(HDRP(NEXT_BLKP(bp))); 
		// Initialize free block header, footer, and epilogue header.
		PUT(HDRP(bp), PACK(size, 0)); 
		PUT(FTRP(bp), PACK(size, 0)); 
// Case 3: the curr block is used but previous block is free while next is taken 
	} else if (!prev_alloc && next_alloc) {         
		// Remove blocks
		remove_block(PREV_BLKP(bp));
		remove_block(bp);
		// Add the size of the previous header.
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		// Initialize free block header, footer, and epilogue header.
		PUT(FTRP(bp), PACK(size, 0));
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		// Update bp to be the previous block of bp.
		bp = PREV_BLKP(bp);
	} else {                                        
		// Remove blocks
		remove_block(NEXT_BLKP(bp));
		remove_block(PREV_BLKP(bp));
		remove_block(bp);
		// Add the size of the previous and next blocks.
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));
		// Initialize free block header, footer, and epilogue header.
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
		// Update bp to be the previous block of bp.
		bp = PREV_BLKP(bp);
		
	}
	// Insert the new block onto the list. 
	insert_block(bp, size);
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	size_t size;
	void *bp;

	// Get the size of the total memory for words.
	size = words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		// Memory request failed.
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

	// Insert the block into the size. 
	insert_block(bp, size);
	return (bp);
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
static void *
find_fit(size_t asize) {
	void *bp;
	// Iterate through the list of blocks.
	for (int range = calc_size(asize); range <= 14; range++) {
		// Get the start of the list for the current range.
		bp = GET_NEXT(heap_listp + (range * WSIZE));
		// Traverse the list for the current range.
		while (bp != NULL) {
		// Check if the block is large enough.
		if (asize <= GET_SIZE(HDRP(bp))) {
			// Found a fit, return the block pointer.
			return bp;
		}
		// Move to the next block in the list.
		bp = GET_NEXT(bp);
		}
	}
	// No fit was found.
	return NULL;
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize) {
    // Get the size of the free block.
    size_t block_size = GET_SIZE(HDRP(bp));
    // Check if the block can be split.
    if ((block_size - asize) >= (2*DSIZE)) {
        // Allocate memory for the first block.
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // Move to the next block.
        bp = NEXT_BLKP(bp);
        // Allocate memory for the second block.
        PUT(HDRP(bp), PACK(block_size - asize, 0));
        PUT(FTRP(bp), PACK(block_size - asize, 0));
        // Insert the second block into the free list.
        insert_block(bp, block_size - asize);
    } else {
        // Allocate memory for the entire block.
        PUT(HDRP(bp), PACK(block_size, 1));
        PUT(FTRP(bp), PACK(block_size, 1));
    }
}


/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp)
{
	if ((uintptr_t)bp % DSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) {
    void *bp;
    // Counters for the free blocks.
    int total = 0;
    int actual = 0;
    if (verbose)
        printf("Heap (%p):\n", heap_listp);
    // Check the prologue.
    if (GET_SIZE(HDRP(heap_listp)) != 19*WSIZE ||
        !GET_ALLOC(HDRP(heap_listp)))
        printf("Bad prologue header\n");
    // Check each block in heap.
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        checkblock(bp);
        // Increment number of free blocks.
        if (!GET_ALLOC(HDRP(bp)))
            total++;
    }
    if (verbose)
        printblock(bp);
    // Check the epilogue.
    if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))
        printf("Bad epilogue header\n");
    // Iterate over each free list in the seg free lists.
    for (int i = 0; i < 14; i++) {
        bp = (char *)GET((i * WSIZE) + heap_listp);
        while (bp != NULL) {
            actual++;

            if (verbose)
                printf("Block of size %lu in bucket: %u\n",
                       GET_SIZE(HDRP(bp)), i);
            // Check that the free lists only contain free blocks.
            if (GET_ALLOC(HDRP(bp)) != 0)
                printf("An allocated block is on the free list\n");
            bp = GET_NEXT(bp);
        }
    }
    // Check if the number of actual free blocks matches total
    if (total != actual)
        printf("Not all of the free blocks are on the free list\n");
}


/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	size_t hsize, fsize;
	bool halloc, falloc;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}
