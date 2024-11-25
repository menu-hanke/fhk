# vim: ft=fhk

### local ffi = require "ffi"
### local info = { a=0, b=0 }
### local fpa = ffi.cast("double (*)()", function() info.a = info.a+1 return info.a end)
### local fpb = ffi.cast("double (*)()", function() info.b = info.b+1 return info.b end)
### G:define(string.format("model global { fpa = 0x%x fpb = 0x%x }", ffi.cast("intptr_t", fpa), ffi.cast("intptr_t", fpb)))

model global {
	a = call C[fpa](): double
	b = call C[fpb](): double
}

### local query = G:newquery("global", "a", "b")
### local reset = G:newreset("global.a")
### compile()
### local inst1 = newinstance()
### check({query.query(inst1):unpack()}, {1,1})
### local inst2 = newinstance(inst1, reset.mask)
### check({query.query(inst2):unpack()}, {2,1})
