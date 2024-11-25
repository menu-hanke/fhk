# vim: ft=fhk

model global {
	a = call Lua["return function(a, b) return a+b end"] (1, 2)
}

### result { a=3 }
