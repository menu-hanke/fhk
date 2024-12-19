# vim: ft=fhk

table t[3]
model t[i] v = [i]

### local ffi = require "ffi"
### local MEM_SIZE, ptr = 4096, 0
### local mem = ffi.new("uint8_t[?]", MEM_SIZE)
### alloc:free()
### alloc = ffi.cast("void *(*)(void *, size_t, size_t)", function(_, size, align)
###     ptr = bit.band(ptr+align-1, bit.bnot(align-1))
###     local ret = mem+ptr
###     ptr = ptr+size
###     assert(ptr <= MEM_SIZE)
###     return ret
### end)
### local queryV0 = G:newquery("global", "t.v[0]")
### local queryV = G:newquery("global", "t.v")
### compile()
### local inst1 = newinstance()
### check({queryV0.query(inst1):unpack()}, {{0}})
### local start = ptr
### local inst2 = newinstance(inst1, 0)
### check({queryV.query(inst2):unpack()}, {{{0},{1},{2}}})
### for i=tonumber(start), MEM_SIZE-1 do mem[i] = 0x29 end
### ptr = start
### check({queryV.query(inst1):unpack()}, {{{0},{1},{2}}})
