# vim: ft=fhk

table tab[3]

model tab[i] {
	a = 2*i
	b = i*i
}

model global {
	tab.x = tab.a + tab.b
	s = sum(tab.x)
}

### result { s=(0+0)+(2+1)+(4+4) }
