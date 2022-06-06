#include "def.h"
#include "target.h"
#include "vm.h"

#include <stddef.h>
#include <stdint.h>

static int map_init(struct fhkX_vmmap *map, intptr_t ptr, size_t size) {
	if(UNLIKELY(!ptr))
		return 0;
	map->base = ptr;
	map->end = ptr + size;
	return 1;
}

#if FHK_MMAP
#include <sys/mman.h>

int fhk_vm_map(struct fhkX_vmmap *map, size_t size) {
	intptr_t base = (intptr_t) mmap(NULL, size, PROT_READ|PROT_WRITE,
			MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);
	return map_init(map, base, size);
}

void fhk_vm_unmap(struct fhkX_vmmap *map) {
	munmap((void *) map->base, map->end - map->base);
}

#elif FHK_WINDOWS
#define WIN32_LEAN_AND_MEAN
#include <windows.h>

int fhk_vm_map(struct fhkX_vmmap *map, size_t size) {
	intptr_t base = (intptr_t) VirtualAlloc(NULL, size, MEM_RESERVE, PAGE_READWRITE);
	map->committed = 0;
	return map_init(map, base, size);
}

void fhk_vm_unmap(struct fhkX_vmmap *map) {
	VirtualFree((LPVOID)map->base, 0, MEM_RELEASE);
}

void fhk_vm_commit(struct fhkX_vmmap *map, intptr_t ptr) {
	if(LIKELY(ptr <= map->committed))
		return;
	// TODO: this needs some error checking.
	VirtualAlloc((LPVOID)map->committed, ptr-map->committed, MEM_COMMIT, PAGE_READWRITE);
	map->committed = ptr;
}

#endif
