# vim: ft=fhk

table tab[3]
model tab[i] x = 2*i
model global s = sum(tab.x)

### result { s=0+2+4 }
