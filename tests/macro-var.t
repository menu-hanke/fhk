# vim: ft=fhk

macro var global rec'{just($x)} = $x
macro var global rec'{add($x,$y)} = rec'{$x} + rec'{$y}
macro var global rec'{mul($x,$y)} = rec'{$x} * rec'{$y}
model global z = rec'{add(just(1),mul(just(2),just(3)))}

### result { z = 1+2*3 }
