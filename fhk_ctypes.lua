local ffi = require "ffi"
local cdef = require "fhk_cdef"
local C = require "fhk_clib"
local band, bor, bnot, i32, lshift, rshift, arshift
	= bit.band, bit.bor, bit.bnot, bit.tobit, bit.lshift, bit.rshift, bit.arshift
local cast = ffi.cast

---- status/error ----------------------------------------

local function ok(status)
	return status >= 0
end

local function errparse(status)
	local code = -tonumber(arshift(status, 58))
	local a = tonumber(band(rshift(status, 52), 0x7))
	local b = tonumber(band(rshift(status, 55), 0x7))
	b = b ~= 0 and b or nil
	local av = bit.tobit(status)
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

---- subsets ----------------------------------------

local emptyset = -1
local undefset = -2

local function i64(x)
	return ffi.cast("int64_t", x)
end

local function u32(x)
	return ffi.cast("uint32_t", x)
end

local function space0(znum)
	return lshift(i64(znum), 43)
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

local function unit(inst)
	return inst
end

local function complex(pkref)
	return bnot(i64(pkref))
end

local function pkpack(pk, first, znum)
	pk[0] = first
	pk[1] = rshift(first, 8)
	pk[2] = bor(band(rshift(first, 16), 0xf), lshift(znum, 4))
	pk[3] = rshift(znum, 4)
	pk[4] = rshift(znum, 12)
end

-- tab must be nonempty and sorted, but may contain duplicates
local function tosubset_nes(tab, alloc)
	local first = tab[1]
	local last = first
	local num = #tab
	local i = 2

	while true do
		if i > num then
			return interval0(first, last-first)
		end

		if tab[i] > last+1 then
			break
		end

		i, last = i+1, tab[i]
	end

	local pks = {}
	local p = 0

	while true do
		pks[p+1] = first
		pks[p+2] = last-first
		p = p+2
		first = tab[i]
		last = first

		while true do
			i = i+1

			if i > num then
				pks[p+1] = first
				pks[p+2] = last-first
				goto out
			end

			if tab[i] > last+1 then
				break
			end

			last = tab[i]
		end
	end

	::out::

	-- (p/2)+1  intervals of 5 bytes each + 3 trailing zero bytes
	local size = 5*(p/2) + 8
	local pkref
	if alloc then
		pkref = ffi.cast("uint8_t *", alloc(size, 1))
	else
		pkref = ffi.new("uint8_t[?]", size)
	end

	local pk = pkref
	for i=0, p, 2 do
		pkpack(pk, pks[i+1], pks[i+2])
		pk = pk + 5
	end
	pk[0] = 0
	pk[1] = 0
	pk[2] = 0

	return complex(pkref), pkref
end

local function tosubset(tab, alloc)
	if #tab == 0 then return emptyset end
	table.sort(tab)
	return tosubset_nes(tab, alloc)
end

local function iscomplex(ss)
	return ss < -1
end

local function pkfirst(pk)
	return bor(pk[0], pk[1], band(pk[2], 0xf))
end

local function pkznum(pk)
	return bor(rshift(pk[2], 4), lshift(pk[3], 4), lshift(pk[4], 12))
end

local function pknext(pk)
	return pk + 5
end

local function pkend(pk)
	return pk[0] == 0 and pk[1] == 0 and pk[2] == 0
end

local function subset_pk(ss)
	return ffi.cast("uint8_t *", bnot(ss))
end

local function sizeof_complex(ss)
	local size = 0
	local pk = subset_pk(ss)
	repeat
		size = size + 1 + pkznum(pk)
		pk = pknext(pk)
	until pkend(pk)
	return size
end

local function interval_first(ss)
	return band(ss, 0xfffff)
end

-- -1 for empty set
local function interval_znum(ss)
	return rshift(i64(ss), 43)
end

-- 0 for emptyset
local function sizeof_interval(ss)
	return 1 + interval_znum(ss)
end

local function sizeof(ss)
	if iscomplex(ss) then
		return sizeof_complex(ss)
	else
		return sizeof_interval(ss)
	end
end

local function interval_tostring(first, znum)
	if znum == 0 then
		return tostring(tonumber(first))
	else
		return string.format("[%d, %d]", first, first+znum)
	end
end

local function subsetstr(ss)
	if ss == emptyset then return "[]" end
	if ss == undefset then return "(undef)" end
	if iscomplex(ss) then
		local intervals = {}
		local pk = subset_pk(ss)
		repeat
			table.insert(intervals, interval_tostring(pkfirst(pk), pkznum(pk)))
			pk = pknext(pk)
		until pkend(pk)
		return string.format("{%s}", table.concat(intervals, ", "))
	else
		return interval_tostring(interval_first(ss), interval_znum(ss))
	end
end

---- guards ----------------------------------------

local nextafter, nextafterf
if jit.os == "Windows" then
	ffi.cdef [[
		float _nextafterf(float from, float to);
		double _nextafter(double from, double to);
	]]
	nextafter, nextafterf = "_nextafter", "_nextafterf"
else
	ffi.cdef [[
		float nextafterf(float from, float to);
		double nextafter(double from, double to);
	]]
	nextafter, nextafterf = "nextafter", "nextafterf"
end

local gvalue = ffi.typeof "fhk_gvalue"

local function tonum(x)
	return tonumber(x) or error(string.format("expected number: %s", x))
end

local function tobits(x)
	if type(x) == "table" then
		local mask = 0LL
		for _,v in ipairs(x) do
			if v >= 64 then error(string.format("bit out of range: %d", v)) end
			mask = bor(mask, lshift(1LL, v))
		end
		return mask
	end
	return tonum(x)
end

local function op(name) return C["FHK_GUARD_"..name:upper()] end
local function ctid(name) return tonumber(ffi.typeof(name)) end
local guards = {
	["&"] = {
		[ctid "uint8_t"] = function(x) return op "u8_m64", gvalue{u64=tobits(x)} end
	},
	["!&"] = {
		[ctid "uint8_t"] = function(x) return op "u8_m64", gvalue{u64=bnot(i64(tobits(x)))} end
	},
	[">="] = {
		[ctid "double"] = function(x) return op "f64_ge", gvalue{f64=tonum(x)} end,
		[ctid "float"]  = function(x) return op "f32_ge", gvalue{f32=tonum(x)} end
	},
	[">"] = {
		[ctid "double"] = function(x) return op "f64_ge", gvalue{f64=ffi.C[nextafter](tonum(x), math.huge)} end,
		[ctid "float"]  = function(x) return op "f32_ge", gvalue{f32=ffi.C[nextafterf](tonum(x), math.huge)} end
	},
	["<="] = {
		[ctid "double"] = function(x) return op "f64_le", gvalue{f64=tonum(x)} end,
		[ctid "float"]  = function(x) return op "f32_le", gvalue{f32=tonum(x)} end
	},
	["<"] = {
		[ctid "double"] = function(x) return op "f64_le", gvalue{f64=ffi.C[nextafter](tonum(x), -math.huge)} end,
		[ctid "float"]  = function(x) return op "f32_le", gvalue{f32=ffi.C[nextafterf](tonum(x), -math.huge)} end
	}
}

local function guard(opcode, arg, ctype)
	opcode = guards[opcode]
	if not opcode then return end
	opcode = opcode[tonumber(ctype)]
	if not opcode then return end
	return opcode(arg)
end

---- build ----------------------------------------

local handles = {
	ident = 0xafffffff,
	space = 0x9fffffff
}

local function handle2(lo, hi)
	return bor(u32(lo), lshift(i64(hi), 32))
end

---- metatypes ----------------------------------------

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

local function parsequery(r)
	if r == -1 then return end -- pruned
	if r == -2 then return true end -- included
	local idx = bit.tobit(r)
	local slot = tonumber(rshift(r, 32))
	return idx, (slot ~= 0 and slot or nil)
end

ffi.metatype("fhk_mut_ref", {
	__index = {
		destroy = C.fhk_destroy_mut,
		layout = function(self) return checkstatus(C.fhk_mut_layout(self)) end,
		prune = function(self) return checkstatus(C.fhk_prune(self)) end,
		query = function(self, handle) return parsequery(C.fhk_mut_query(self, handle)) end,
		size = function(self)
			local size = C.fhk_mut_size(self)
			return size > 0 and size or nil
		end,
		build = function(self, p)
			local status = C.fhk_mut_build(self, p)
			if ok(status) then
				return ffi.cast("fhk_graph *", status)
			else
				return nil, err(status)
			end
		end,
		pin = C.fhk_mut_pin,
		add_group = function(self) return checkhandle(C.fhk_mut_add_group(self)) end,
		add_mapk = function(self) return checkhandle(C.fhk_mut_add_mapK(self)) end,
		add_mapi = function(self) return checkhandle(C.fhk_mut_add_mapI(self)) end,
		add_model = function(self, group, k, c)
			return checkhandle(C.fhk_mut_add_model(self, group, k or (0/0), c or (0/0)))
		end,
		add_var = function(self, group) return checkhandle(C.fhk_mut_add_var(self, group)) end,
		add_guard = function(self, var) return checkhandle(C.fhk_mut_add_guard(self, var)) end,
		add_param = function(self, model, var, map) return checkhandle(C.fhk_mut_add_param(self, model, var, map)) end,
		add_return = function(self, model, var, map) return checkhandle(C.fhk_mut_add_return(self, model, var, map)) end,
		add_check = function(self, model, guard, map, penalty)
			return checkhandle(C.fhk_mut_add_check(self, model, guard, map, penalty or math.huge))
		end,
		set_dsym = C.fhk_mut_set_dsym,
		set_cost = function(self, model, k, c)
			C.fhk_mut_set_costM(self, model, k or (0/0), c or (0/0))
		end,
		set_size = function(self, var, size)
			return checkstatus(C.fhk_mut_set_sizeV(self, var, size))
		end,
		set_opcode = function(self, guard, opcode, arg)
			return checkstatus(C.fhk_mut_set_opcodeG(self, guard, opcode, arg))
		end
	}
})

local function mrefp(b, p)
	return cast("uint8_t *", b) + p
end

ffi.metatype("fhk_mem", {
	__index = {
		destroy = C.fhk_destroy_mem,
		reset = C.fhk_reset_mem
	},
	__call = C.fhk_mem_alloc
})


local function solver_mem(S)
	return cast("fhk_mem *", mrefp(S, S.mem))
end

ffi.metatype("fhk_solver", {
	__index = {
		continue = function(self)
			local status = C.fhk_continue(self)
			if not ok(status) then return errparse(status) end
		end,
		setshape = C.fhk_setshape,
		setshapeT = C.fhk_setshapeT,
		setroot = C.fhk_setroot,
		setrootC = C.fhk_setrootC,
		setrootD = C.fhk_setrootD,
		setmapK = C.fhk_setmapK,
		setmapI = C.fhk_setmapI,
		setvalue = C.fhk_setvalue,
		setvalueC = C.fhk_setvalueC,
		setvalueD = C.fhk_setvalueD,
		copysubset = C.fhk_copysubset,
		getmem = solver_mem
	}
})

local function gc(x)
	if x.destroy then
		ffi.gc(x, x.destroy)
		return x
	end
end

local function mem()
	local r = C.fhk_create_mem()
	return r ~= nil and r or nil
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

local function solver(G, m)
	if m then
		return C.fhk_create_solver(G, m)
	else
		m = mem()
		return ffi.gc(C.fhk_create_solver(G, m),  function() C.fhk_destroy_mem(m) end)
	end
end

--------------------------------------------------------------------------------

return {
	ok        = ok,
	err       = err,
	emptyset  = emptyset,
	undefset  = undefset,
	space0    = space0,
	space1    = space1,
	interval0 = interval0,
	interval1 = interval1,
	unit      = unit,
	complex   = complex,
	tosubset  = tosubset,
	sizeof    = sizeof,
	subsetstr = subsetstr,
	guard     = guard,
	handles   = handles,
	handle2   = handle2,
	gc        = gc,
	mem       = mem,
	mut       = mut,
	solver    = solver,
	dsym      = C.fhk_is_dsym() ~= 0
}
