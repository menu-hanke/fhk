# vim: ft=fhk

### local ffi = require "ffi"
### local info = { a=0, b=0 }
### local fpa = ffi.cast("double (*)()", function() info.a = info.a+1 return info.a end)
### local fpb = ffi.cast("double (*)()", function() info.b = info.b+1 return info.b end)
### G:define(string.format("model global { fpa = effect(0x%x, state.reset_a) fpb = effect(0x%x, state.reset_b) }", ffi.cast("intptr_t", fpa), ffi.cast("intptr_t", fpb)))

model global {
	a = call C[fpa](): double
	b = call C[fpb](): double
}

### local query = G:query("a", "b")
### compile()
### local inst1 = newinstance()
### check({image[query](inst1):unpack()}, {1,1})
### local inst2 = newinstance(inst1, {reset_a=true})
### check({image[query](inst2):unpack()}, {2,1})
