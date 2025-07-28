# vim: ft=fhk

table t[3]
model t[i] x = 2*i where i>0
func getxi(i) = t.x[i]

model global {
	x0 = getxi(0)
	x0 = -1
	x1 = getxi(1)
}

### result {x0=-1, x1=2}
