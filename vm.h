#pragma once

#include "def.h"
#include "target.h"

#include <stddef.h>
#include <stdint.h>

typedef struct fhkX_vmmap {
	intptr_t base;
	intptr_t end;
#if FHK_WINDOWS
	intptr_t committed;
#endif
} fhkX_vmmap;

NOAPI int fhk_vm_map(struct fhkX_vmmap *map, size_t size);
NOAPI void fhk_vm_unmap(struct fhkX_vmmap *map);

#if FHK_MMAP
#define fhk_vm_commit(map, ptr)
#endif

#if FHK_WINDOWS
NOAPI void fhk_vm_commit(struct fhkX_vmmap *map, intptr_t ptr);
#endif
