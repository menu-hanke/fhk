# vim: ft=fhk

model global {
	A: [:,:] = call R["function() cbind(c(1,2), c(3,4))"] ()
	b: [:] = call R["colSums"] (A)
}

### result { b={3,7} }
