# vim: ft=fhk

table t[:,[1,2,3]]
model global t.x[::] = [1, 2, 3, 4, 5, 6]

### result { ["t.x"]={{1},{2,3},{4,5,6}} }
