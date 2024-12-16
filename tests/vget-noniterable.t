# vim: ft=fhk

table t[5]

model global {
	t.a = [1, 2, 3, 4, 5]
	t.b = [0, 1, 0, 1, 0]
	ab = t.a[which(t.b=1)]
	s = sum(ab)
}

### result { s=2+4 }
