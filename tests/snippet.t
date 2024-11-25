# vim: ft=fhk

macro number 123

macro binop'($x $op $y) $x $op $y

macro definemodel'{$res, $op, $x, $y} {
	model global $res = ~binop'[$x $op $y]
}

macro %private'{$x, $value} {
	model global $x = $value
}

~%private'{x,7}
~definemodel'{y,+,x,~number}

### result { y=130 }
