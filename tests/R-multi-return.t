# vim: ft=fhk

model global {
	a, b = call R["function() list(1,2)"] ()
}

### result {a=1, b=2}
