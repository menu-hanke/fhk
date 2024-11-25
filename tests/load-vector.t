# vim: ft=fhk

table A[3]
model global s = sum(A.x)

### ffi = require "ffi"
### v = ffi.new("double[3]", {1,2,3})
### G:define(string.format("model global A.x = load'f64(0x%x, 3)", ffi.cast("intptr_t", ffi.cast("void *", v))))
### result { s=1+2+3 }
