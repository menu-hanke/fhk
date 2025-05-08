# vim: ft=fhk

model global s=1
model global where true and true {
	x = 1 where s=1
	x = 0
}

### result { x=1 }
