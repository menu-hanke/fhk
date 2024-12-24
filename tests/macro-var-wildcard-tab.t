# vim: ft=fhk

macro var $table eval'$expr = $expr

table tab[3]

model global {
	tab.x = [1,2,3]
	tab.y = [4,5,6]
	tab.z = tab.eval'{x+y}
}

### result { ["tab.z"]={1+4,2+5,3+6} }
