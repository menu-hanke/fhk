# vim: ft=fhk

table A[2]
table B[:,[2,3]]

model global A.x = [1,2]
model B x = A.x

### result { ["B.x"]={{1,1},{2,2,2}} }
