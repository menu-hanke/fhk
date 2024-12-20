# vim: ft=fhk

table t[3]
model global t.xs = load'f64(load'ptr(dataptr), 3)

### local ffi = require "ffi"
### local data1 = ffi.new("double[?]", 3, {1,2,3})
### local data2 = ffi.new("double[?]", 3, {4,5,6})
### local dataptr = ffi.new("double *[1]")
### dataptr[0] = data1
### G:define(string.format("model global dataptr = 0x%x", ffi.cast("intptr_t", dataptr)))
### local query = G:newquery("global", "t.xs")
### local reset = G:newreset("t.xs")
### compile()
### local inst1 = newinstance()
### check({query.query(inst1):unpack()}, {{1,2,3}})
### dataptr[0] = data2
### local inst2 = newinstance(inst1, reset.mask)
### check({query.query(inst2):unpack()}, {{4,5,6}})
