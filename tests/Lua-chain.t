# vim: ft=fhk

model global {
	a = call Lua ["return function() return 1 end"] ()
	b = call Lua ["return function() return 2 end"] ()
	c = call Lua ["return function(a,b,c,d) return a+b+c+d end"] (a, a, b, 3)
}

### result { c=1+1+2+3 }
