# vim: ft=fhk

### local ffi = require "ffi"
### local fp = ffi.cast("double (*)(int)", function(v) return k*v end)
### G:define(string.format("model global fp = 0x%x", ffi.cast("intptr_t", fp)))

table t[10]
model t[i] ki = call C[global.fp](i: int): double
model global s = sum(t.ki)

### local query = G:newquery("global", "s")
### local reset = G:newreset("t.ki")
### compile()
### k = 1
### local inst1 = newinstance()
### check({query.query(inst1):unpack()}, {45})
### k = 2
### local inst2 = newinstance(inst1, reset.mask)
### check({query.query(inst2):unpack()}, {2*45})
