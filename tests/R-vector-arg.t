# vim: ft=fhk

model global {
	s = call R["sum"]([1,2,3])
}

### result { s=6 }
