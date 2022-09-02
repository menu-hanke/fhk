#pragma once

/* initial k for models. */
#define INIT_K                   1.0

/* initial c for models. */
#define INIT_C                   1.5

/*
 * virtual memory mapping size (bytes).
 * fhk will never remap its memory area, so this should be large enough.
 */
#define VM_SIZE                  (1ULL << 32)

/* candidate heap copy unroll factor. */
#define SOLVER_HEAP_COPY_UNROLL  4

/* solver call stack size (bytes). */
#define MAX_STACK                8192

/* initial mutgraph size (bytes). */
#define MUT_INIT_UP              1024
#define MUT_INIT_DOWN            1024

/* initial pruning heap size (slots). */
#define BHEAP_INIT               64

/* tracing options */
#ifndef FHK_TRACE
#define FHK_TRACE
#endif
