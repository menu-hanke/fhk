# vim: ft=fhk

model global {
	a = all([true])
	b = all([true, false])
	c = any([true, false])
	d = any([false, false, false])
	e = all(a, b, c, d)
	f = any(a, b, c, d)
	g = all()
	h = any()
}

### result { a=true, b=false, c=true, d=false, e=false, f=true, g=true, h=false }
