#include "arena.h"
#include "def.h"
#include "trace.h"

#include <stddef.h>
#include <stdlib.h>

static mem_chunk *chunk_alloc(size_t hint){
	mem_chunk *chunk = malloc(sizeof(*chunk) + hint);
	chunk->end = (intptr_t)chunk + sizeof(*chunk) + hint;
	return chunk;
}

static void arena_init(struct fhk_arena *arena, mem_chunk *chunk){
	arena->chunk = chunk;
	chunk->prev = NULL;
	chunk->next = NULL;
}

void fhk_init_arena(struct fhk_arena *arena, size_t hint){
	arena_init(arena, chunk_alloc(hint));
	arena->ptr = chunk_start(arena->chunk);
}

struct fhk_arena *fhk_create_arena(size_t hint){
	mem_chunk *chunk = chunk_alloc(sizeof(struct fhk_arena) + hint);
	struct fhk_arena *arena = (struct fhk_arena *) chunk_start(chunk);
	arena_init(arena, chunk);
	arena->ptr = (intptr_t)arena + sizeof(struct fhk_arena);
	return arena;
}

void fhk_destroy_arena(struct fhk_arena *arena){
	mem_chunk *chunk = arena->chunk;
	while(chunk->next) chunk = chunk->next;
	for(;;){
		mem_chunk *prev = chunk->prev;
		free(chunk);
		if(!prev)
			break;
		chunk = prev;
	}
}

void *fhk_alloc(struct fhk_arena *arena, size_t size, size_t align){
	intptr_t ptr = ALIGN(arena->ptr, align);
	intptr_t end = ptr + size;
	mem_chunk *chunk = arena->chunk;
	if(LIKELY(end < chunk->end)){
		arena->ptr = end;
		trace(ALLOC, size, align, (void*)ptr);
		return (void *) ptr;
	}

	for(;;){
		mem_chunk *next = chunk->next;
		if(!next)
			break;

		chunk = next;
		intptr_t ptr = ALIGN(chunk_start(chunk), align);
		intptr_t end = ptr + size;
		if(LIKELY(end < chunk->end)){
			arena->chunk = chunk;
			arena->ptr = ptr;
			return (void *) ptr;
		}
	}

	trace(OVERFLOW, size, align);

	size_t newsize = chunk_size(chunk);
	do {
		newsize <<= 1;
	} while(newsize < size+align-1);
	mem_chunk *next = chunk_alloc(newsize);
	next->prev = chunk;
	next->next = NULL;
	chunk->next = next;
	arena->chunk = next;
	ptr = ALIGN(chunk_start(next), align);
	arena->ptr = ptr + size;
	return (void *) ptr;
}
