# vim: ft=fhk

table A[2]
table B[:, A.N]

model A[i] {
	B_x = [1,2] where i=0
	B_x = [3,4,5] where i=1
	N = len(B_x)
	B.x = B_x
}

### result { ["B.x"] = {{1,2},{3,4,5}} }
