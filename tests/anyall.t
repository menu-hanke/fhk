# vim: ft=fhk

model global {
	a = all([true])
	b = all([true, false])
	c = any([true, false])
	d = any([false, false, false])
}

### result { a=true, b=false, c=true, d=false }
