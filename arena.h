#pragma once

#include <stdint.h>

typedef struct mem_chunk {
	struct mem_chunk *prev, *next;
	intptr_t end;
} mem_chunk;

#define chunk_start(chunk) ((intptr_t)(chunk) + sizeof(mem_chunk))
#define chunk_size(chunk)  ((chunk)->end - chunk_start(chunk))

typedef struct fhk_arena {
	mem_chunk *chunk;
	intptr_t ptr;
} fhk_arena;
