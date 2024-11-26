# vim: ft=fhk

model global x = 0

model global where x >= 0 {
	y = 1 where x > 0
	y = 2
}

model global where x < 0 {
	y = 3
}

### result { y=2 }
