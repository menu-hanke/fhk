# vim: ft=fhk

model global {
	a = call R["function(a, b) a+b"] (1, 2)
}

### result { a=3 }
