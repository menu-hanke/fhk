# vim: ft=fhk

model global {
	a = call C[fptr] (1: double, 2: double): double
}

### fptr = require("ffi").cast("double (*)(double, double)", function(a, b) return a+b end)
### G:define(string.format("model global { fptr = 0x%x }", require("ffi").cast("intptr_t", fptr)))
### result { a=3 }
