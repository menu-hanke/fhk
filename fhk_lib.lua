local function groupof(name)
	return name:match("^(.-)#(.*)$")
end

local function ungroup(name)
	local _,name = groupof(name)
	return name
end

local function matchname(a, b)
	local ga, na = groupof(a)
	local gb, nb = groupof(b)
	if (na or a) ~= (nb or b) then return false end
	if ga and gb and ga ~= gb then return false end
	return true
end

return {
	groupof   = groupof,
	ungroup   = ungroup,
	matchname = matchname
}
