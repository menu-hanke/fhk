local ffi = require "ffi"
local cdef = require "fhk_cdef"
local C = require "fhk_clib"
local cast, sizeof = ffi.cast, ffi.sizeof
local intptr, uint8p, int64_t = ffi.typeof("intptr_t"), ffi.typeof("uint8_t *"), ffi.typeof("int64_t")
local arshift, band, bnot, bor, i32, lshift, rshift
	= bit.arshift, bit.band, bit.bnot, bit.bor, bit.tobit, bit.lshift, bit.rshift

local function i64(n)
	return cast(int64_t, n)
end

---- subsets ----------------------------------------

local emptyset = -1

local function space0(znum)
	return lshift(i64(znum), 32)
end

local function space1(size)
	if size == 0 then
		return emptyset
	else
		return space0(size-1)
	end
end

local function interval0(first, znum)
	return bor(first, space0(znum))
end

local function interval1(first, size)
	if size == 0 then
		return emptyset
	else
		return interval0(first, size-1)
	end
end

local function complex(ptr)
	return bnot(i64(ptr))
end

local function pkpack(pk, first, znum)
	pk[0] = first
	pk[1] = rshift(first, 8)
	pk[2] = bor(band(rshift(first, 16), 0xf), lshift(znum, 4))
	pk[3] = rshift(znum, 4)
	pk[4] = rshift(znum, 12)
end

local function tosubset_sorted_nonempty(tab, alloc)
	local first = tab[1]
	local last = first
	local num = #tab
	local i = 2
	while true do
		if i>num then
			return interval0(first, last-first)
		end
		local j = tab[i]
		if j > last+1 then break end
		i, last = i+1, j
	end
	local pk = {[0]=first, [1]=last}
	local pki = 2
	while true do
		first = tab[i]
		last = first
		i = i+1
		while true do
			if i>num then
				pk[pki] = first
				pk[pki+1] = last
				goto out
			end
			local j = tab[i]
			if j > last+1 then
				pk[pki] = first
				pk[pki+1] = last
				pki = pki+2
				break
			end
			i, last = i+1, j
		end
	end
	::out::
	-- 5 bytes per interval (pki/2+1 intervals) + 3 trailing zero bytes
	local size = 5*(pki/2)+8
	local pkref
	if alloc then
		pkref = cast(uint8p, alloc(size, 1))
	else
		pkref = ffi.new("uint8_t[?]", size)
	end
	local p = pkref
	for i=0, pki, 2 do
		pkpack(p, pk[i], pk[i+1]-pk[i])
		p = p+5
	end
	p[0] = 0
	p[1] = 0
	p[2] = 0
	return complex(pkref), pkref
end

local function tosubset(tab, alloc)
	if #tab == 0 then return emptyset end
	table.sort(tab)
	return tosubset_sorted_nonempty(tab, alloc)
end

---- status/error ----------------------------------------

local function ok(status)
	return status >= 0
end

local function errparse(status)
	local code = -tonumber(arshift(status, 58))
	local a = tonumber(band(rshift(status, 52), 0x7))
	if a == 0 then a = nil end
	local b = tonumber(band(rshift(status, 55), 0x7))
	if b == 0 then b = nil end
	local av = a and i32(status)
	local bv = b and tonumber(band(rshift(status, 32), 0xfffff))
	return code, a, av, b, bv
end

local err_mt = {
	__tostring = function(self)
		local msg = cdef.errmsg[self.code]
		for _,tag in pairs(cdef.errtag) do
			if self[tag] then
				msg = string.format("%s (%s: %s)", msg, tag, self[tag])
			end
		end
		return msg
	end
}

local function err(status)
	local code, a, av, b, bv = errparse(status)
	local err = setmetatable({ code=code }, err_mt)
	if a then err[cdef.errtag[a]] = av end
	if b then err[cdef.errtag[b]] = bv end
	return err
end

local function checkhandle(status)
	if ok(status) then
		return i32(status)
	else
		return nil, err(status)
	end
end

local function checkstatus(status)
	if not ok(status) then
		return err(status)
	end
end

---- building graphs ----------------------------------------

-- note: this must match the definitions in build.h
local mref_start  = tonumber(ffi.offsetof("fhk_mut_graph", "mem"))
local mref_ident  = mref_start
local mref_global = mref_ident + ffi.sizeof("fhk_mut_var")
local mtagp       = ffi.typeof("fhk_mtag *")

local function qparse(query)
	if query == -1 then return end
	local j = i32(query)
	local i = i32(rshift(query, 32))
	return i, j >= 0 and j or nil
end

local function omask(m)
	local out = 0
	for i=1, #m do
		out = bor(out, cdef.mtagmask[m:sub(i,i)])
	end
	return out
end

local function mut_opairs(mref, mask, match)
	if type(mask) == "string" then
		local mask_, match_ = mask:match("^(%w+)=(%w*)$")
		if mask_ then
			mask, match = mask_, match_
		end
		mask = omask(mask)
	end
	if type(match) == "string" then
		match = omask(match)
	end
	if mask and not match then
		match = mask
	end
	local used = mref.mp.uused
	local ref = mref_start
	local function nextobj()
		if ref >= used then return end
		-- mref may be reallocated while the iterator is running so we have to re-fetch base here.
		local base = cast(intptr, mref.mp)
		local tag = cast(mtagp, base+ref)[0]
		local otype = cdef.otype[band(tag, 7)]
		local handle = ref
		ref = ref + otype.size
		if mask and band(tag, mask) ~= match then
			return nextobj()
		else
			return handle, cast(otype.ctypeptr, base+handle)
		end
	end
	return nextobj
end

local function mut_get(mref, handle)
	local base = cast(intptr, mref.mp)
	local tag = cast(mtagp, base+handle)[0]
	return cast(cdef.otype[band(tag, 7)].ctypeptr, base+handle)
end

---- solver inspection ----------------------------------------

local function solver_V(S, idx)
	return ffi.cast("void **", S+1)[idx]
end

local function solver_X(S, idx)
	return ffi.cast("fhk_sp **", S)[bit.bnot(idx)]
end

---- metatypes ----------------------------------------

for tag,ct in pairs {
	var       = "fhk_mut_var",
	model     = "fhk_mut_model",
	predicate = "fhk_mut_predicate",
	edge      = "fhk_mut_edge",
	rcheck    = "fhk_mut_retcheck",
	check     = "fhk_mut_check"
} do
	ffi.metatype(ct, {
		__index = { what = tag }
	})
end

ffi.metatype("fhk_mut_ref", {
	__index = {
		destroy = C.fhk_destroy_mut,
		set_default_cost = C.fhk_mut_set_default_cost,
		add_var = function(self, group) return checkhandle(C.fhk_mut_add_var(self, group)) end,
		set_inverse = function(self, map, inverse) return checkstatus(C.fhk_mut_set_inverse(self, map, inverse)) end,
		set_lhs = function(self, guard, var) return checkstatus(C.fhk_mut_set_lhs(self, guard, var)) end,
		set_size = function(self, var, size) return checkstatus(C.fhk_mut_set_size(self, var, size)) end,
		add_model = function(self, group) return checkhandle(C.fhk_mut_add_model(self, group)) end,
		set_cost = C.fhk_mut_set_cost,
		add_param = function(self, model, var, map) return checkhandle(C.fhk_mut_add_param(self, model, var, map)) end,
		add_return = function(self, model, var, map) return checkhandle(C.fhk_mut_add_return(self, model, var, map)) end,
		add_check = function(self, model, guard, map, penalty)
			return checkhandle(C.fhk_mut_add_check(self, model, guard, map, penalty or math.huge))
		end,
		add_rcheck = function(self, edge, check, penalty)
			return checkhandle(C.fhk_mut_add_rcheck(self, edge, check, penalty or math.huge))
		end,
		add_predicate = function(self) return checkhandle(C.fhk_mut_add_predicate(self)) end,
		set_operator = function(self, obj, operator, operand)
			return checkstatus(C.fhk_mut_set_operator(self, obj, operator, operand))
		end,
		set_predicate = function(self, obj, pre) return checkstatus(C.fhk_mut_set_predicate(self, obj, pre)) end,
		disable = C.fhk_mut_disable,
		analyze = function(self) return checkstatus(C.fhk_mut_analyze(self)) end,
		mark = function(self, obj) return checkstatus(C.fhk_mut_mark(self, obj)) end,
		layout = function(self) return checkstatus(C.fhk_mut_layout(self)) end,
		size = C.fhk_mut_size,
		build = function(self, buf)
			local r = C.fhk_mut_build(self, buf)
			if ok(r) then
				return ffi.cast("fhk_graph *", r)
			else
				return nil, err(r)
			end
		end,
		query = function(self, obj) return qparse(C.fhk_mut_query(self, obj)) end,
		opairs = mut_opairs,
		get = mut_get
	}
})

ffi.metatype("fhk_mem", {
	__index = {
		destroy = C.fhk_destroy_mem,
		reset = C.fhk_reset_mem
	}
})

ffi.metatype("fhk_solver", {
	__index = {
		V = solver_V,
		X = solver_X
	}
})

local function gc(x)
	ffi.gc(x, x.destroy)
	return x
end

local function mut(mp)
	mp = mp or ffi.new("fhk_mut_ref")
	local status = C.fhk_create_mut(mp)
	if ok(status) then
		return mp
	else
		return nil, err(status)
	end
end

local function mem()
	return C.fhk_create_mem()
end

local function solver(mem, G)
	return C.fhk_create_solver(mem, G)
end

--------------------------------------------------------------------------------

return {
	emptyset    = emptyset,
	space0      = space0,
	space1      = space1,
	interval0   = interval0,
	interval1   = interval1,
	tosubset    = tosubset,
	err         = err,
	gc          = gc,
	mut         = mut,
	mem         = mem,
	solver      = solver,
	mref_global = mref_global,
	mref_ident  = mref_ident
}
