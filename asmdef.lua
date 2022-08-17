local ffi = require "ffi"
require "fhk_cdef"
-- yes, this is technically not portable.
-- this technically does not work if we are cross-compiling between 32/64-bit targets.
-- BUT: fhk doesn't support targets with 32-bit pointer size anyway. so no problem here.
print("#define SIZEOF_fhk_solver " .. ffi.sizeof("fhk_solver"))
print("#define OFFSETOF_sref_err " .. ffi.offsetof("fhk_solver", "err") - ffi.sizeof("fhk_solver"))
