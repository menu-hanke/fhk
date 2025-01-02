# vim: ft=fhk

table B[:,[2,3,4]]

model global {
	B.x[::] = [1,2,3,4,5,6,7,8,9]
	x = sum(B.x[([0,2],:)])
}

### result { x=1+2+6+7+8+9 }
