#pragma once

/* max work stack size.
 * one slot = 8 bytes
 */
#define FHK_MAX_STACK              1024

/* max cost.
 * anything above this is considered infinity.
 * this must be a positive floating point number,
 * but it may be smaller than FLT_MAX.
 */
#include <float.h>
#define FHK_MAX_COST               FLT_MAX

/* initial size of mut graph, in both directions, in bytes.
 * must be aligned to 4.
 */
#define FHK_MUT_SIZE               1024

/* initial size of bound heap, in bound slots of 8 bytes each */
#define FHK_BHEAP_SIZE             64

/* coroutine stack size.
 * must be aligned to 16.
 */
#define FHK_MAX_COSTACK            (1024*64)

/* coroutine implementation. you probably want to set this in the makefile.
 * libco is the slow, portable fallback implementation.
 */
#ifndef FHK_CO
#define FHK_CO                     libco
#endif

/* tracing options */
#ifndef FHK_TRACE
#define FHK_TRACE
#endif
