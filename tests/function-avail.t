# vim: ft=fhk

func getx() = x
func gety() = y

model global {
	x = 1 where false
	y = 2
	a = getx()
	a = gety()
}

### result {a=2}
