# vim: ft=fhk

table t[3]
model global t.xs = effect(load'f64(load'ptr(dataptr), 3), state.reset1)

### local ffi = require "ffi"
### local data1 = ffi.new("double[?]", 3, {1,2,3})
### local data2 = ffi.new("double[?]", 3, {4,5,6})
### local dataptr = ffi.new("double *[1]")
### dataptr[0] = data1
### G:define(string.format("model global dataptr = 0x%x", ffi.cast("intptr_t", dataptr)))
### local query = G:query("t.xs")
### compile()
### local inst1 = newinstance()
### check({image[query](inst1):unpack()}, {{1,2,3}})
### dataptr[0] = data2
### local inst2 = newinstance(inst1, {reset1=true})
### check({image[query](inst2):unpack()}, {{4,5,6}})
