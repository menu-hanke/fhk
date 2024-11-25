# vim: ft=fhk

table t[3]

model t[i] {
	x = 100*i
	rev = 2-i
}

model global v = t.x[...t.rev]

### result { v={200, 100, 0} }
