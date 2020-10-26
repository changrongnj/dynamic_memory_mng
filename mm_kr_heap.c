/*
 * mm_kr_heap.c
 *
 * Based on C dynamic memory manager code from
 * Brian Kernighan and Dennis Richie (K&R)
 *
 *  @since Feb 13, 2019
 *  @author philip gust
 *  @modified rong chang
 */


#include <stdio.h>
#include <unistd.h>
#include <stddef.h>
#include <string.h>
#include <stdbool.h>
#include <errno.h>
#include <assert.h>
#include "memlib.h"
#include "mm_heap.h"


/** Allocation unit for header of memory blocks */
typedef union Header {
    struct {
        union Header *ptr;  /** next block if on free list */
        size_t size;        /** size of this block including header */
                            /** measured in multiple of header size */
    } s;
    max_align_t _align;     /** force alignment to max align boundary */
} Header;

// forward declarations
static Header *morecore(size_t);
void visualize(const char*);
inline static Header *mm_next(Header *bp);
inline static void mm_unlink(Header *bp);

/*
 * Check whether multiply overflows (true if overflow)
 * Extracted from:
 *   https://github.com/Cloudef/chck/blob/master/chck/overflow/overflow.h
 */
#ifndef __has_builtin
#define __has_builtin(x) 0
#endif
#if __GNUC__ >= 5 || __has_builtin(__builtin_add_overflow)
/* assume clang and gcc (>=5) to only have builtins for now. */
#define mul_of(a, b, r) __builtin_mul_overflow(a, b, r)
#else
/* else use generic, note behaviour is not strictly defined in C. */
#define mul_of(a, b, r) (((*(r) = ((a) * (b))) || *(r) == 0) && ((a) != 0 && (b) > *(r) / (a)))
#endif

static bool debug = false;
/** Start of free memory list */
static Header *freep = NULL;
/**
 * Initialize memory allocator
 */
void mm_init(void) {
	mem_init();
    freep = NULL;
}

/**
 * Reset memory allocator.
 */
void mm_reset(void) {
    if (debug) visualize("RESET");
    mem_reset_brk();
    freep = NULL;
}

/**
 * De-initialize memory allocator.
 */
void mm_deinit(void) {
	mem_deinit();
    freep = NULL;
}

/**
 * Allocation units for nbytes bytes.
 *
 * @param nbytes number of bytes
 * @return number of units for nbytes
 */
inline static size_t mm_units(size_t nbytes) {
    /* smallest count of Header-sized memory chunks */
    /*  (+1 additional chunk for the Header itself) needed to hold nbytes */
    return (nbytes + 2 * sizeof(Header) - 1) / sizeof(Header) + 1;
}

/**
 * Allocation bytes for nunits allocation units.
 *
 * @param nunits number of units
 * @return number of bytes for nunits
 */
inline static size_t mm_bytes(size_t nunits) {
    return nunits * sizeof(Header);
}

/**
 * Get pointer to block payload.
 *
 * @param bp the block
 * @return pointer to allocated payload
 */
inline static void *mm_payload(Header *bp) {
	return bp + 1;
}

/**
 * Get pointer to block for payload.
 *
 * @param ap the allocated payload pointer
 */
inline static Header *mm_block(void *ap) {
	return (Header*)ap - 1;
}
/**
 *  get pointer to block footer from header pointer 
 *
 * @param hp the header pointer
 */
inline static Header *mm_footer(Header *hp) {      
    return hp + hp->s.size - 1;
}
/**
 * get pointer to block header from footer pointer
 *
 * @param ap the footer pointer
 */
inline static Header *mm_header(Header *fp) {
    return fp - fp->s.size + 1;
}

/**
 * get size of blocks in header units
 *
 * @param bp the block pointer
 */
inline static size_t mm_size(Header *bp) {
    return bp->s.size;
}
/**
 * set size of block in header units 
 *
 * @param bp the block pointer
 */
inline static void mm_setSize(Header *bp, size_t size) {
    bp->s.size = size;
    mm_footer(bp)->s.size = size;
}
/**
 * get next block in free list
 *
 * @param bp the block pointer
 */
inline static Header *mm_next(Header *bp) {
    return bp->s.ptr;
}
/**
 * set next block in free list
 *
 * @param bp the block pointer
 * @param next the next block pointer 
 */
inline static void mm_setNext(Header *bp, Header *next) {
    bp->s.ptr = next;
}
/**
 * get prev block in free list
 *
 * @param bp the block pointer
 */
inline static Header *mm_prev(Header *bp) {
   return mm_footer(bp)->s.ptr;
}
/**
 * set prev block in free list
 *
 * @param bp the block pointer
 * @param prev the prev block pointer 
 */
inline static void mm_setPrev(Header *bp, Header *prev) {
    mm_footer(bp)->s.ptr = prev;
}
/**
 * get block before in memory (NULL if no block) 
 *
 * @param bp the block pointer
 */
inline static Header * mm_before(Header *bp) {
    if ((void *) bp <= mem_heap_lo()) {
        return NULL;
    }
    return mm_header(bp - 1);
}
/**
 * get block after in memory (NULL if no block)
 *
 * @param bp the block pointer
 */
inline static Header * mm_after(Header *bp) {
    if ((void *)(bp + bp->s.size) > mem_heap_hi()) {
        return NULL;
    }
    return bp + bp->s.size;
}

/**
 * unlink the block from free list
 *
 * @param bp the block pointer
 */
inline static void mm_unlink(Header *bp) {
    if (mm_next(bp) == bp) {
        mm_setNext(bp, NULL);
        mm_setPrev(bp, NULL);
        freep = NULL;
        return;
    }
    else {
        Header * prev = mm_prev(bp);
        Header * next = mm_next(bp);
        mm_setNext(prev, next);
        mm_setPrev(next, prev);
        mm_setNext(bp, NULL);
        mm_setPrev(bp, NULL);
    }

}

/**
 * link block into free list
 *
 * @param bp the block pointer
 */
inline static void mm_link(Header *bp, Header *pos) {
    if (pos == NULL) {
        mm_setNext(bp, bp);
        mm_setPrev(bp, bp);
        freep = bp;
        return;
    }
    Header *prev = mm_prev(pos);
    mm_setNext(prev, bp);
    mm_setPrev(bp, prev);
    mm_setNext(bp, pos);
    mm_setPrev(pos, bp);
}
/**
 * Allocates size bytes of memory and returns a pointer to the
 * allocated memory, or NULL if request storage cannot be allocated.
 *
 * @param nbytes the number of bytes to allocate
 * @return pointer to allocated memory or NULL if not available.
 */
void *mm_malloc(size_t nbytes) {
    if (debug) visualize("PRE-MALLOC");
    Header *p = NULL;
    size_t nunits = mm_units(nbytes);
    if (debug) fprintf(stderr, "nunits %zu\n", nunits);
    if (freep == NULL) {
        p = morecore(nunits);
        if (p == NULL) {
            errno = ENOMEM;
            return NULL;                /* none left */
        }
        freep = p;
    }

    // smallest count of Header-sized memory chunks
    //  (+1 additional chunk for the Header itself) needed to hold nbytes
    // traverse the circular list to find a block
    for (p = mm_next(freep); true ; p = mm_next(p)) {
        if (p->s.size >= nunits) {          /* found block large enough */
            if (debug) fprintf(stderr,"Found block %10p to allocate, size %zu \n", (void*) p, p->s.size);
            if (p->s.size == nunits || p->s.size == nunits + 1) {
				// free block exact size
                if (debug) fprintf(stderr,"Exact fit \n"); 
                if (freep == p) freep = mm_prev(p);             
                mm_unlink(p);
            } else {
            	// split and allocate tail end
                if (debug) fprintf(stderr,"Split \n");
                Header *prev = mm_prev(p); 
                Header *next = mm_next(p);
                mm_setSize(p, mm_size(p) - nunits);
                mm_setPrev(p, prev);
                mm_setNext(p, next);
                if (debug) fprintf(stderr,"First block in split size %zu\n", p->s.size);
                /* find the address to return */
                p += mm_size(p);		 // address upper block to return
                mm_setSize(p, nunits);
                mm_setNext(p, NULL);
                mm_setPrev(p, NULL);
                if (debug) fprintf(stderr,"Second block in split size %zu\n", p->s.size);
                freep = prev;
            }
            if (debug) visualize("POST-MALLOC");
            return mm_payload(p);
        }

        /* back where we started and nothing found - we need to allocate */
        if (p == freep) {                    /* wrapped around free list */
        	p = morecore(nunits);
        	if (p == NULL) {
                errno = ENOMEM;
                return NULL;                /* none left */
            }
            freep = mm_prev(p);
        }
    }

    assert(false);  // shouldn't happen
	return NULL;
}


/**
 * Deallocates the memory allocation pointed to by ap.
 * If ap is a NULL pointer, no operation is performed.
 *
 * @param ap the memory to free
 */
void mm_free(void *ap) {
    if (debug) visualize("PRE-FREE");
	// ignore null pointer
    if (ap == NULL) {
        return;
    }

    Header *bp = mm_block(ap);   /* point to block header */
    // validate size field of header block
    assert(bp->s.size > 0 && mm_bytes(bp->s.size) <= mem_heapsize());
    if (freep == NULL) { /* the list is empty. Add the first block to list */
        if (debug) fprintf(stderr,"Empty free list. Init\n");
        mm_setNext(bp, bp);
        mm_setPrev(bp, bp);
        freep = bp;
        return;
    }
    Header *pnext = NULL;
    Header *p = NULL;
    if (mm_after(bp) != NULL && mm_after(bp)->s.ptr != NULL) {
		/* coalesce if adjacent to upper neighbor
         *  unlink the upper block from free list and coalese
         */
        if (debug) fprintf(stderr,"Coalese upper \n");
        pnext = mm_after(bp);
        /* If the block to unlink happen to be freep, reset freep */
        if (freep == pnext) freep = mm_prev(pnext); 
        mm_unlink(pnext); 
        mm_setSize(bp, mm_size(bp) + mm_size(pnext));
        mm_setNext(bp, NULL);
        mm_setPrev(bp, NULL);     
    }
    
    if (mm_before(bp) != NULL && mm_before(bp)->s.ptr != NULL) {
        /* coalesce if adjacent to lower block
         *  unlink the lower block from free list and coalese
         */
        if (debug) fprintf(stderr,"Coalese lower \n");
        p = mm_before(bp);
        /* If the block to unlink happen to be freep, reset freep */
        if (freep == p) freep = mm_prev(p);
        mm_unlink(p);
        mm_setSize(p, mm_size(p) + mm_size(bp));
        mm_setNext(bp, NULL);
        mm_setPrev(bp, NULL);
        mm_setNext(p, NULL);
        mm_setPrev(p, NULL);
        // reset bp to where p is
        bp = p;     
    }
    /* link bp into the free list at freep, 
     * bp could have been coaesced with upper/lower block already
     */
    mm_link(bp, freep);
    /* reset the start of the free list */
    freep = mm_prev(bp);
    if (debug) visualize("POST-FREE");
}

/**
 * Tries to change the size of the allocation pointed to by ap
 * to size, and returns ap.
 *
 * If there is not enough room to enlarge the memory allocation
 * pointed to by ap, realloc() creates a new allocation, copies
 * as much of the old data pointed to by ptr as will fit to the
 * new allocation, frees the old allocation, and returns a pointer
 * to the allocated memory.
 *
 * If ap is NULL, realloc() is identical to a call to malloc()
 * for size bytes.  If size is zero and ptr is not NULL, a minimum
 * sized object is allocated and the original object is freed.
 *
 * @param ap pointer to allocated memory
 * @param newsize required new memory size in bytes
 * @return pointer to allocated memory at least required size
 *	with original content
 */
void* mm_realloc(void *ap, size_t newsize) {
	// NULL ap acts as malloc for size newsize bytes
	if (ap == NULL) {
		return mm_malloc(newsize);
	}

	Header* bp = mm_block(ap);    // point to block header
	if (newsize > 0) {
		// return this ap if allocated block large enough
		if (bp->s.size >= mm_units(newsize)) {
			return ap;
		}
	}

	// allocate new block
	void *newap = mm_malloc(newsize);
	if (newap == NULL) {
		return NULL;
	}
	// copy old block to new block
	size_t oldsize = mm_bytes(bp->s.size-1);
	memcpy(newap, ap, (oldsize < newsize) ? oldsize : newsize);
	mm_free(ap);
	return newap;
}

/**
 * Contiguously allocates enough space for count objects that are
 * size bytes of memory each and returns a pointer to the allocated
 * memory.  The allocated memory is filled with bytes of value zero.
 *
 * @param count the number of blocks to allocate
 * @param size the size of each element
 * @return pointer to allocated memory or NULL if not available.
 */
void* mm_calloc(size_t count, size_t size) {
	// multiply and check for overflow: not available
	// in standard C and K&R version ignored overflow
	size_t nbytes; // product
	if (mul_of(count, size, &nbytes)) { // overflow if true
		return NULL;
	}

	void* p = mm_malloc(nbytes);
	if (p != NULL) {
		memset(p, 0, nbytes);
	}
	return p;
}

/**
 * Request additional memory to be added to this process.
 *
 * @param nu the number of Header units to be added
 * @return pointer to start additional memory added
 */
static Header *morecore(size_t nu) {
	// nalloc based on page size
	size_t nalloc = mem_pagesize()/sizeof(Header);

    /* get at least NALLOC Header-chunks from the OS */
    if (nu < nalloc) {
        nu = nalloc;
    }

    size_t nbytes = mm_bytes(nu); // number of bytes
    void* p = mem_sbrk(nbytes);
    if (p == (char *) -1) {	// no space
        return NULL;
    }

    Header* bp = (Header*)p;
    // Need to set size for both header and footer
    mm_setSize(bp, nu);
    // add new space to the circular list
    mm_free(bp+1);

    return freep;
}

/**
 * Print the free list (debugging only)
 *
 * @msg the initial message to print
 */
void visualize(const char* msg) {
    fprintf(stderr, "\n--- Free list after \"%s\":\n", msg);

    if (freep == NULL) {                   /* does not exist */
        fprintf(stderr, "    List is empty or not exist\n\n");
        return;
    }

    if (freep == freep->s.ptr) {          /* self-pointing list = empty */
        fprintf(stderr, "    List has 1 block\n\n");
        char* str = "    ";
        fprintf(stderr, "%sptr: %10p size: %3lu blks - %5lu bytes\n", str, (void *)freep, freep->s.size, mm_bytes(freep->s.size));
        return;
    }

    char* str = "    ";
    for (Header *p = mm_next(freep); true; p = p->s.ptr) {
        fprintf(stderr, "%sptr: %10p size: %3lu blks - %5lu bytes\n", 
        	str, (void *)p, p->s.size, mm_bytes(p->s.size));
        str = " -> ";
        if ( p == freep) break;
    }


    fprintf(stderr, "--- end\n\n");
}


/**
 * Calculate the total amount of available free memory.
 *
 * @return the amount of free memory in bytes
 */
size_t mm_getfree(void) {
    if (freep == NULL) {
        return 0;
    }

	// point to head of free list
    Header *tmp = freep;
    size_t res = tmp->s.size;

	// scan free list and count available memory
    while (tmp->s.ptr > tmp) {
        tmp = tmp->s.ptr;
        res += tmp->s.size;
    }

	// convert header units to bytes
    return mm_bytes(res);
}
