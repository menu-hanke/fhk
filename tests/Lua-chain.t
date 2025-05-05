# vim: ft=fhk

model global {
	a = call Lua ["return function() return 1 end"] ()
	b = call Lua ["return function() return 2 end"] ()
	c = call Lua ["return function(a,b,c) return a+b+c end"] (a, b, 3)
}

### result { c=1+2+3 }
