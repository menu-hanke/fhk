local function a_mod(x, y)
	local sum = 0
	for _,v in ipairs(y) do
		sum = sum + v
	end
	return sum, x*sum
end

return {
	a_mod = a_mod
}
