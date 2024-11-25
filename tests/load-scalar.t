# vim: ft=fhk

### ffi = require "ffi"
### v = ffi.new("double[1]", {123})
### G:define(string.format("model global v = load'f64(0x%x)", ffi.cast("intptr_t", ffi.cast("void *", v))))
### result { v=123 }
