#pragma once

#include "def.h"
#include <stdint.h>

/* TODO: this needs a cleanup. in the future this file should not exist,
 * but the jump tables should go in either the solver or graph,
 * and the state should go in solver.
 * then fhk_continue gets the signature:
 *     int fhk_continue(fhk_solver *)
 * the return value is the jtab entry.
 */

typedef union fhk_jtab_offset {
	int16_t jcode[6];
	struct {
		int16_t ok;
		int16_t shape;
		int16_t vref;
		int16_t mapcallk;
		int16_t mapcalli;
		int16_t modcall;
	};
} fhk_jtab_offset;

typedef struct fhk_jtab_state {
	union {
		fhk_status status;
		fhk_modcall *modcall;
		struct {
			int32_t idx;
			int32_t inst;
		};
	};
	fhk_jtab_offset index;
} fhk_jtab_state;

int fhk_jtab_continue(fhk_solver *S, fhk_jtab_state *J);
