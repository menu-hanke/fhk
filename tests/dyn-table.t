# vim: ft=fhk

table dyn[:,[1,2,3]]
model dyn[i,j] x = 100*i + j

### result { ["dyn.x"]={{0},{100,101},{200,201,202}} }
