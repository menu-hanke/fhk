# vim: ft=fhk

model global {
	x = 123
	y = 2 where x < 0
	y = 4 where x >= 0
	z = 3 where x > 0
	z = 4
}

### result { y=4, z=3 }
