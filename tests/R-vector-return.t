# vim: ft=fhk

table tab[3]
model global {
	tab.x = call R["function() c(1,2,3)"] ()
}

### result { ["tab.x"]={1,2,3} }
