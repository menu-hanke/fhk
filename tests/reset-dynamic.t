# vim: ft=fhk

### local ffi = require "ffi"
### local fp = ffi.cast("double (*)(int)", function(v) return k*v end)
### G:define(string.format("model global fp = effect(0x%x,state.reset1)", ffi.cast("intptr_t",fp)))

table t[10]
model t[i] ki = call C[global.fp](i: int): double
model global s = sum(t.ki)

### local query = G:query("s")
### G:query("t.ki[0]") -- prevent inlinining the call so it's actually reset
### compile()
### k = 1
### local inst1 = newinstance()
### check({image[query](inst1):unpack()}, {45})
### k = 2
### local inst2 = newinstance(inst1, {})
### check({image[query](inst2):unpack()}, {45})
### local inst3 = newinstance(inst1, {reset1=true})
### check({image[query](inst3):unpack()}, {2*45})
