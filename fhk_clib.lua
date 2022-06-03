require "fhk_cdef"
local ffi = require "ffi"
if pcall(function() return ffi.C.fhk_create_solver end) then
	return ffi.C
else
	return ffi.load("fhk")
end
