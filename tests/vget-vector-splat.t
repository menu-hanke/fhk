# vim: ft=fhk

table A[2]
table B[:,A.N]

model global {
	A.N = [2, 3]
	B.x[::] = [1, 2, 3, 4, 5]
}

# XXX: the [..v] here is supposed to be a blackbox that makes the vget materialized.
# replace with blackbox(...) when it's implemented.
model A x = sum([..B.x])

### result { ["A.x"] = {1+2, 3+4+5} }
