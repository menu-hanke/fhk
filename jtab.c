#include "fhk.h"
#include "def.h"
#include "jtab.h"

int fhk_jtab_continue(fhk_solver *S, fhk_jtab_state *J){
	fhk_status status = fhk_continue(S);
	if(UNLIKELY(fhk_status_iserr(status))){
		J->status = status;
		return 0;
	}

	int code = fhk_status_code(status);
	if(code == FHKS_MODCALL){
		J->modcall = fhk_status_mcall(status);
		return J->index.modcall + J->modcall->idx;
	}else{
		J->idx = fhk_status_idx(status);
		J->inst = fhk_status_inst(status);
		// note: OK is all zeros, so D->idx=0 if code=FHK_OK.
		return J->index.jcode[code] + J->idx;
	}
}
