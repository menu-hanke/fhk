table T[5]

model global {
	T.x = [1, 2, 3, 4, 5]
	T.y = [10, 100, 1000, 10000, 100000]
	idx = [2,4]
	T.z = T.x[idx]/T.y[idx]
}

### result { ["T.z"]={3/1000, 5/100000} }
