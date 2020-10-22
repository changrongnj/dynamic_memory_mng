/*
 * mm_heap.h
 *
 * This file contains definitions of the functions
 * that must be implemented by a memory manager.
 *
 *  @since 2019-02-27
 *  @author philip gust
 */

#ifndef MM_HEAP_H_
#define MM_HEAP_H_

/**
 * Initialize memory allocator.
 */
void mm_init(void);

/**
 * Reset memory allocator.
 */
void mm_reset(void);

/**
 * De-initialize memory allocator.
 */
void mm_deinit(void);

/**
 * Calculate the total amount of available free memory.
 *
 * @return the amount of free memory in bytes
 */
size_t mm_getfree(void);


/**
 * Allocates size bytes of memory and returns a pointer to the
 * allocated memory, or NULL if request storage cannot be allocated.
 *
 * @param nbytes the number of bytes to allocate
 * @return pointer to allocated memory or NULL if not available.
 */
void *mm_malloc(size_t nbytes);

/**
 * Contiguously allocates enough space for count objects that are
 * size bytes of memory each and returns a pointer to the allocated
 * memory.  The allocated memory is filled with bytes of value zero.
 *
 * @param count the number of blocks to allocate
 * @param size the size of each element
 * @return pointer to allocated memory or NULL if not available.
 */
void* mm_calloc(size_t count, size_t size);

/**
 * Deallocates the memory allocation pointed to by ptr.
 * if ptr is a NULL pointer, no operation is performed.
 *
 * @param ap the allocated block to free
 */
void mm_free(void *ap);

/**
 * Reallocates size bytes of memory and returns a pointer to the
 * allocated memory, or NULL if request storage cannot be allocated.
 *
 * @param ap the currently allocated storage
 * @param nbytes the number of bytes to allocate
 * @return pointer to allocated memory or NULL if not available.
 */
void *mm_realloc(void *ap, size_t size);


#endif /* MM_HEAP_H_ */