# cython: language_level=3

#---- lua state ----------------------------------------

cdef extern from *:
    """
    #include "def.h"
    #include "fhk.h"
    #include "solve.h"

    #include <lua.h>
    #include <lauxlib.h>
    #include <lualib.h>

    #define RKEY_NEW       "!@fhk_pyx_new"
    #define RKEY_SOLVER    "!@fhk_pyx_solver"
    #define RKEY_READY     "!@fhk_pyx_ready"
    #define RKEY_READ      "!@fhk_pyx_read"

    static void copyregfield(lua_State *L, const char *field, const char *rkey) {
        // registry[rkey] = top[field]
        lua_getfield(L, -1, field);
        lua_setfield(L, LUA_REGISTRYINDEX, rkey);
    }

    static void *fhk_pyx_initlua() {
        lua_State *L = luaL_newstate();
        if(!L) return NULL;
        luaL_openlibs(L);
        lua_getfield(L, LUA_GLOBALSINDEX, "require");
        lua_pushliteral(L, "fhk_pyx");
        lua_call(L, 1, 1);
        copyregfield(L, "new",    RKEY_NEW);
        copyregfield(L, "solver", RKEY_SOLVER);
        copyregfield(L, "ready",  RKEY_READY);
        copyregfield(L, "read",   RKEY_READ);
        lua_pop(L, 1);
        return L;
    }

    static const char *fhk_pyx_err(lua_State *L) {
        return lua_tostring(L, -1);
    }

    #define fhk_pyx_closelua lua_close

    static int fhk_pyx_new(lua_State *L, void *o) {
        lua_getfield(L, LUA_REGISTRYINDEX, RKEY_NEW);
        lua_pushlightuserdata(L, o);
        if(lua_pcall(L, 1, 1, 0))
            return LUA_NOREF;
        return luaL_ref(L, LUA_REGISTRYINDEX);
    }

    static int fhk_pyx_solver(lua_State *L, int ref, void *o) {
        lua_getfield(L, LUA_REGISTRYINDEX, RKEY_SOLVER);
        lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
        lua_pushlightuserdata(L, o);
        if(lua_pcall(L, 2, 1, 0))
            return -1;
        int r = lua_tointeger(L, -1);
        lua_pop(L, 1);
        return r;
    }

    static int fhk_pyx_read(lua_State *L, int ref, void *fname) {
        lua_getfield(L, LUA_REGISTRYINDEX, RKEY_READ);
        lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
        lua_pushlightuserdata(L, fname);
        return lua_pcall(L, 2, 0, 0);
    }

    static int fhk_pyx_ready(lua_State *L, int ref) {
        lua_getfield(L, LUA_REGISTRYINDEX, RKEY_READY);
        lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
        if(lua_pcall(L, 1, 1, 0))
            return LUA_NOREF;
        return luaL_ref(L, LUA_REGISTRYINDEX);
    }

    static int fhk_pyx_refsolver(lua_State *L, int ref, int idx) {
        lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
        lua_rawgeti(L, -1, idx);
        int r = luaL_ref(L, LUA_REGISTRYINDEX);
        lua_pop(L, 1);
        return r;
    }

    static int fhk_pyx_callinit(lua_State *L, int ref, fhk_mem *mem, void *X) {
        lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
        lua_pushlightuserdata(L, X);
        lua_pushlightuserdata(L, mem);
        if(lua_pcall(L, 2, 1, 0))
            return LUA_NOREF;
        return luaL_ref(L, LUA_REGISTRYINDEX);
    }

    static int fhk_pyx_callsolver(lua_State *L, int fref, int Sref, void *X,
        void *result, void *subsets) {
        lua_rawgeti(L, LUA_REGISTRYINDEX, fref);
        lua_rawgeti(L, LUA_REGISTRYINDEX, Sref);
        lua_pushlightuserdata(L, X);
        lua_pushlightuserdata(L, result);
        lua_pushlightuserdata(L, subsets);
        return lua_pcall(L, 4, 0, 0);
    }

    static void fhk_pyx_unref(lua_State *L, int ref) {
        luaL_unref(L, LUA_REGISTRYINDEX, ref);
    }
    """
    ctypedef long fhk_subset
    ctypedef struct fhk_mem
    fhk_mem *fhk_create_mem()
    void fhk_destroy_mem(fhk_mem *mem)
    void fhk_reset_mem(fhk_mem *mem)
    int LUA_NOREF
    ctypedef struct lua_State
    lua_State *fhk_pyx_initlua()
    void fhk_pyx_closelua(lua_State *)
    const char *fhk_pyx_err(lua_State *)
    int fhk_pyx_new(lua_State *, void *)
    int fhk_pyx_solver(lua_State *, int, void *)
    int fhk_pyx_read(lua_State *, int, void *)
    int fhk_pyx_ready(lua_State *, int)
    int fhk_pyx_refsolver(lua_State *, int, int)
    int fhk_pyx_callinit(lua_State *, int, fhk_mem *, void *)
    int fhk_pyx_callsolver(lua_State *, int, int, void *, void *, void *)
    void fhk_pyx_unref(lua_State *, int)

class LuaError(RuntimeError):
    pass

cdef class LuaState:
    cdef lua_State *L

    def __cinit__(self):
        self.L = fhk_pyx_initlua()
        if self.L == NULL:
            raise RuntimeError("failed to create lua state")

    def __dealloc__(self):
        fhk_pyx_closelua(self.L)

    def new(self, view):
        return self._checkref(fhk_pyx_new(self.L, <void*>view))

    def solver(self, state, roots):
        idx = fhk_pyx_solver(self.L, state, <void*>roots)
        if idx < 0:
            raise LuaError(fhk_pyx_err(self.L))
        return idx

    def read(self, state, fname):
        self._checkpcall(fhk_pyx_read(self.L, state, <void*>fname))

    def ready(self, state):
        return Pin(self, self._checkref(fhk_pyx_ready(self.L, state)))

    def pinsolver(self, state, idx):
        return Pin(self, self._checkref(fhk_pyx_refsolver(self.L, state, idx)))

    cpdef callinit(self, Pin init, Mem mem, state):
        return Pin(self, self._checkref(fhk_pyx_callinit(self.L, init.ref, mem.mem, <void*>state)))

    cpdef callsolver(self, Pin fn, Pin solver, state, result, subsets):
        self._checkpcall(fhk_pyx_callsolver(
            self.L,
            fn.ref,
            solver.ref,
            <void*>state,
            <void*>result,
            <void*>subsets
        ))

    def unref(self, ref):
        fhk_pyx_unref(self.L, ref)

    def _checkpcall(self, r):
        if r != 0:
            raise LuaError(fhk_pyx_err(self.L))

    def _checkref(self, ref):
        if ref == LUA_NOREF:
            raise LuaError(fhk_pyx_err(self.L))
        return ref

cdef class Pin:
    cdef LuaState lua
    cdef int ref

    def __cinit__(self, lua, ref):
        self.lua = lua
        self.ref = ref

    def __dealloc__(self):
        if self.lua is not None:
            fhk_pyx_unref(self.lua.L, self.ref)

cdef class Mem:
    cdef fhk_mem *mem

    def __cinit__(self):
        self.mem = fhk_create_mem()

    def __dealloc__(self):
        fhk_destroy_mem(self.mem)

    def reset(self):
        fhk_reset_mem(self.mem)

#---- subset functions ----------------------------------------

cdef extern from *:
    fhk_subset SUBSET_EMPTY
    fhk_subset subsetI_newZ(int, int)

cdef public fhk_subset fhk_pyx_tosubset(void *op):
    o = <object> op
    if isinstance(o, int):
        return o
    raise NotImplementedError("TODO: convert subset")

def interval(start, num):
    if num == 0:
        return SUBSET_EMPTY
    return subsetI_newZ(num-1, start)

def space(num):
    return interval(0, num)
