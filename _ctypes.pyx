# cython: language_level=3
cimport cython
from libc.stdint cimport uint8_t, int16_t, int32_t, int64_t
from cpython.mem cimport PyMem_RawFree
from cpython.ref cimport Py_DECREF
from collections import namedtuple
from array import array
from struct import unpack, pack_into
from typing import TypeVar, Generic

cdef extern from "<lua.h>":
    ctypedef double lua_Number
    ctypedef ptrdiff_t lua_Integer
    ctypedef struct lua_State
    int lua_gettop(lua_State *L)
    void lua_settop(lua_State *L, int idx)
    int lua_type(lua_State *L, int idx)
    lua_Number lua_tonumber(lua_State *L, int idx)
    int lua_toboolean(lua_State *L, int idx)
    const char *lua_tolstring(lua_State *L, int idx, size_t *len)
    void *lua_topointer(lua_State *L, int idx)
    void lua_pushnumber(lua_State *L, lua_Number n)
    void lua_pushinteger(lua_State *L, lua_Integer n)
    void lua_pushlstring(lua_State *L, const char *s, size_t l)
    void lua_pushlightuserdata(lua_State *L, void *p)
    void lua_gettable(lua_State *L, int idx);
    void lua_getfield(lua_State *L, int idx, const char *k)
    void lua_rawgeti(lua_State *L, int idx, int n)
    void lua_settable(lua_State *L, int idx)
    void lua_pop(lua_State *L, int n)
    const char *lua_tostring(lua_State *L, int i)

    int LUA_REGISTRYINDEX
    int LUA_TNIL
    int LUA_TBOOLEAN
    int LUA_TLIGHTUSERDATA
    int LUA_TNUMBER
    int LUA_TSTRING
    int LUA_TTABLE
    int LUA_TFUNCTION
    int LUA_TUSERDATA
    int LUA_TTHREAD

cdef extern from *:
    """
    #define FHK_PY_CALL      "!@fhk_py_call"
    #define FHK_PY_ADDREF    "!@fhk_py_addref"
    #define FHK_PY_READY     "!@fhk_py_ready"

    #include "def.h"
    #include "fhk.h"
    #include "solve.h"

    #include <lauxlib.h>
    #include <lualib.h>

    static void copyregfield(lua_State *L, const char *field, const char *rkey) {
        // registry[rkey] = top[field]
        lua_getfield(L, -1, field);
        lua_setfield(L, LUA_REGISTRYINDEX, rkey);
    }

    /* leaves module on top of stack */
    static lua_State *fhk_py_setup_lua() {
        lua_State *L = luaL_newstate();
        if(!L) return NULL;
        luaL_openlibs(L);
        lua_getfield(L, LUA_GLOBALSINDEX, "require");
        lua_pushliteral(L, "fhk_py");
        lua_call(L, 1, 1);
        copyregfield(L, "call", FHK_PY_CALL);        // registry[FHK_PY_CALL]   = fhk_py.calll
        copyregfield(L, "addref", FHK_PY_ADDREF);    // registry[FHK_PY_ADDREF] = fhk_py.addref
        copyregfield(L, "ready", FHK_PY_READY);      // registry[FHK_PY_READY]  = fhk_py.ready
        return L;
    }

    static void fhk_py_close_lua(lua_State *L) {
        lua_close(L);
    }

    /* leaves ref cdata on top of stack */
    static void fhk_py_lua_pushref(lua_State *L, void *pyobj) {
        // cdata, isnew = addref(pyobj)
        lua_getfield(L, LUA_REGISTRYINDEX, FHK_PY_ADDREF);
        lua_pushlightuserdata(L, pyobj);
        lua_call(L, 1, 2);
        if(lua_toboolean(L, -1))
            Py_INCREF(pyobj);
        lua_pop(L, 1);
    }

    /* pops cdata from stack.
     * note that if it's not a python ref cdata this will break catastrophically. */
    static void *fhk_py_lua_popref(lua_State *L) {
        void *pyobj = *(void**)lua_topointer(L, -1);
        Py_INCREF(pyobj);
        return pyobj;
    }

    #define fhk_py_lua_ref(L)      luaL_ref((L), LUA_REGISTRYINDEX)
    #define fhk_py_lua_unref(L,r)  luaL_unref((L), LUA_REGISTRYINDEX, (r))

    /* stack must be prepared for a `lua_call` of registry[FHK_PY_CALL].
     * return -1 -> call failed, only error message is left on stack
     * otherwise -> call ok, return value is previous stack top, returns are on top of stack */
    static int fhk_py_lua_ecall(lua_State *L, int narg) {
        int top = lua_gettop(L) - (narg+1);
        if(top < 0) __builtin_unreachable();
        lua_call(L, narg, LUA_MULTRET);
        if(lua_toboolean(L, top+1)) {
            return top;
        } else {
            lua_remove(L, -2);
            return -1;
        }
    }

    static int fhk_py_lua_callsx(lua_State *L, int ref, fhk_solver *S, void *X) {
        lua_getfield(L, LUA_REGISTRYINDEX, FHK_PY_CALL);
        lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
        lua_pushlightuserdata(L, S);
        lua_pushlightuserdata(L, X);
        return fhk_py_lua_ecall(L, 3); // ->0
    }

    static int fhk_py_lua_ready(lua_State *L, int ref, fhk_graph **G, int *init, int *jump) {
        lua_getfield(L, LUA_REGISTRYINDEX, FHK_PY_CALL);
        lua_getfield(L, LUA_REGISTRYINDEX, FHK_PY_READY);
        lua_rawgeti(L, LUA_REGISTRYINDEX, ref);
        lua_pushlightuserdata(L, G);
        if(fhk_py_lua_ecall(L, 3) < 0) // ->2
            return -1;
        *jump = fhk_py_lua_ref(L);
        *init = fhk_py_lua_ref(L);
        return 0;
    }

    /* access macros, since cython isn't very good at structs. */
    #define fhk_py_var_group(G,i) (G)->vars[(i)].group
    #define fhk_py_var_size(G,i)  (G)->vars[(i)].size
    #define fhk_py_G(S)           (S)->G
    #define fhk_py_space(S,i)     anymapK((S)->map[(i)])
    """

    ctypedef struct fhk_mem
    ctypedef struct fhk_graph
    ctypedef struct fhk_solver
    ctypedef int64_t fhk_subset
    ctypedef int16_t fhkP_idx

    fhk_subset SUBSET_EMPTY
    fhk_subset subsetI_newZ(int zs, int first)

    fhk_mem *fhk_create_mem()
    void fhk_destroy_mem(fhk_mem *mem)
    fhk_solver *fhk_create_solver(fhk_graph *G, fhk_mem *mem)
    void fhk_setshape(fhk_solver *S, int group, int shape)
    void *fhk_setrootD(fhk_solver *S, int idx, fhk_subset ss)
    void fhk_setvalueC(fhk_solver *S, int idx, fhk_subset ss, void *p)

    int subset_isU(fhk_subset ss)
    int subsetIE_size(fhk_subset ss)

    const char *FHK_PY_CALL

    lua_State *fhk_py_setup_lua()
    void fhk_py_close_lua(lua_State *L)
    void fhk_py_lua_pushref(lua_State *L, void *pyobj)
    void *fhk_py_lua_popref(lua_State *L)
    int fhk_py_lua_ref(lua_State *L)
    void fhk_py_lua_unref(lua_State *L, int r)
    int fhk_py_lua_ecall(lua_State *L, int nargs);
    int fhk_py_lua_callsx(lua_State *L, int ref, fhk_solver *S, void *X)
    int fhk_py_lua_ready(lua_State *L, int ref, fhk_graph **G, int *init, int *jump)

    int fhk_py_var_group(fhk_graph *G, int i)
    int fhk_py_var_size(fhk_graph *G, int i)
    fhk_graph *fhk_py_G(fhk_solver *S)
    fhk_subset fhk_py_space(fhk_solver *S, int i)

#---- subsets ----------------------------------------

cdef fhk_subset tosubset(x):
    if isinstance(x, int):
        return x
    raise NotImplementedError("TODO: new allocator api & subset builders")

def interval(start, num):
    if num == 0:
        return SUBSET_EMPTY
    return subsetI_newZ(num-1, start)

def space(num):
    return interval(0, num)

#---- callbacks ----------------------------------------
# keep in sync with fhk_py.lua!

cdef public void fhk_py_gc(void *p):
    Py_DECREF(<object> p)

cdef public void fhk_py_call1(void *p, void *a):
    (<object> p) (<object> a)

cdef public double fhk_py_vref_scalar_fp(void *p, void *X, int inst):
    return (<object> p) (<object> X, inst)

cdef public int64_t fhk_py_vref_scalar_int(void *p, void *X, int inst):
    return (<object> p) (<object> X, inst)

cdef public void fhk_py_vref_vector(
    fhk_solver *S,
    int idx,
    void *p,
    void *X,
    int inst,
    int32_t flags
):
    vec, ss_ = (<object> p)(<object> X, inst)
    cdef fhk_subset ss = tosubset(ss_)
    cdef str typecode = chr(flags & 0xff)
    # TODO: this is a slow but easy way to do it.
    # probably the fastest solution is to move the unpacking to Lua,
    # so that we can easily specialize on the ctype.
    # (ie. code gen per-ctype a scatter function that calls fhk_setvalueD then scatters
    #  the python iterable. this needs python api on the lua side and is a lot of work though...)
    # TODO 2: if vec is an array or a (contiguous) numpy array with the correct typecode,
    # we could fhk_setvalue it here directly.
    tmp = array(typecode, vec)
    if len(tmp) != subsetIE_size(ss): # TODO: complex subsets
        # we can't raise here, but solver will throw since we didn't give it a value
        return
    # python docs are trying to tell me to use the buffer protocol api but this is a lot easier :^)
    ptr, _ = tmp.buffer_info()
    fhk_setvalueC(S, idx, ss, <void*><size_t>ptr)

cdef public fhk_subset fhk_py_getmapK(void *p, void *X):
    return tosubset((<object> p) (<object> X))

cdef public fhk_subset fhk_py_getmapI(void *p, void *X, int inst):
    return tosubset((<object> p) (<object> X, inst))

class FhkError(Exception):
    pass

#---- lua state ----------------------------------------

cdef class GCLua:
    cdef lua_State *L
    cdef GCPin _fhk_py

    def __cinit__(self):
        self.L = fhk_py_setup_lua()
        if self.L is NULL:
            raise FhkError("failed to create Lua state")
        # fhk_py module is on top of stack
        self._fhk_py = pin(self)

    def __dealloc__(self):
        fhk_py_close_lua(self.L)

    @property
    def fhk_py(self):
        return self._fhk_py

cdef GCPin pin(GCLua lua):
    return GCPin(lua, fhk_py_lua_ref(lua.L))

cdef void push(GCLua lua, x):
    # add new cases as needed.
    if isinstance(x, GCPin):
        lua_rawgeti(lua.L, LUA_REGISTRYINDEX, (<GCPin> x)._ref)
    elif isinstance(x, bytes):
        lua_pushlstring(lua.L, x, len(x))
    elif isinstance(x, str):
        push(lua, x.encode("utf8"))
    elif isinstance(x, int):
        lua_pushinteger(lua.L, x)
    elif isinstance(x, float):
        lua_pushnumber(lua.L, x)
    elif hasattr(x, "__lua__"):
        push(lua, x.__lua__(lua))
    else:
        fhk_py_lua_pushref(lua.L, <void*>x)

cdef void push2(GCLua lua, a, b):
    push(lua, a)
    push(lua, b)

cdef void push3(GCLua lua, a, b, c):
    push(lua, a)
    push(lua, b)
    push(lua, c)

cdef object pop(GCLua lua):
    # add new cases as needed.
    L = lua.L
    t = lua_type(L, -1)
    if t == LUA_TTABLE or t == LUA_TFUNCTION:
        return pin(lua)
    elif t == 10: # cdata
        return <object> fhk_py_lua_popref(L)
    if t == LUA_TNUMBER:
        x = lua_tonumber(L, -1)
    elif t == LUA_TSTRING:
        x = lua_tostring(L, -1).decode("utf8")
    elif t == LUA_TBOOLEAN:
        x = bool(lua_toboolean(L, -1))
    elif t == LUA_TNIL:
        x = None
    else:
        raise FhkError(f"pop what?: {t}")
    lua_pop(L, 1)
    return x

@cython.freelist(16)
cdef class GCPin:
    cdef GCLua _lua
    cdef int _ref

    def __cinit__(self, lua, ref):
        self._lua = lua
        self._ref = ref

    def __dealloc__(self):
        # Python seems to set this to None when the interpreter is shutting down,
        # before calling __dealloc__.
        # If I'm reading the docs correctly this is guaranteed since all references
        # (to the GCLua) must be gone before its __dealloc__ is called.
        # Also lupa has this same check so I suppose it's sufficient.
        if self._lua is not None:
            fhk_py_lua_unref(self._lua.L, self._ref)

    def __setitem__(self, key, value):
        push3(self._lua, self, key, value)
        lua_settable(self._lua.L, -3)
        lua_pop(self._lua.L, 1)

    def __setattr__(self, key, value):
        self.__setitem__(key, value)

    def __getitem__(self, key):
        push2(self._lua, self, key)
        lua_gettable(self._lua.L, -2)
        x = pop(self._lua)
        lua_pop(self._lua.L, 1)
        return x

    def __getattr__(self, key):
        return self.__getitem__(key)

    def __call__(self, *args):
        L = self._lua.L
        lua_getfield(L, LUA_REGISTRYINDEX, FHK_PY_CALL)
        push(self._lua, self)
        for x in args:
            push(self._lua, x)
        top = fhk_py_lua_ecall(L, len(args)+1)
        if top >= 0:
            nret = lua_gettop(L)-top-1
            r = [None]*nret
            for i in range(nret):
                r[nret-i-1] = pop(self._lua)
            lua_settop(L, top)
            return r
        else:
            raise FhkError(pop(self._lua))

#---- solver ----------------------------------------

cdef class GCMem:
    cdef fhk_mem *mem

    def __cinit__(self):
        self.mem = fhk_create_mem()

    def __dealloc__(self):
        fhk_destroy_mem(self.mem)

cdef class GCDriver:
    cdef fhk_graph *G
    cdef GCLua lua
    cdef int init
    cdef int jump

    def __dealloc__(self):
        PyMem_RawFree(self.G)

cdef class GCSolver:
    cdef fhk_solver *S
    # these fields are only for holding a reference to prevent gc.
    # we are in trouble if the mem or graph gets gced while the solver is running.
    cdef GCMem _mem
    cdef GCDriver _driver

cdef class CRoot:
    cdef str name
    cdef str fmt
    cdef object vector
    cdef fhkP_idx idx

    def __init__(self, name, fmt, vector, idx):
        self.name = name
        self.fmt = fmt
        self.vector = vector
        self.idx = idx

def newlua():
    return GCLua().fhk_py

def ready(GCPin state):
    cdef fhk_graph *G
    cdef int init
    cdef int jump
    if fhk_py_lua_ready(state._lua.L, state._ref, &G, &init, &jump) < 0:
        raise FhkError(pop(state._lua))
    cdef GCDriver driver = GCDriver()
    driver.G = G
    driver.lua = state._lua
    driver.init = init
    driver.jump = jump
    return driver

def init(GCDriver driver, GCMem gcm, X):
    cdef fhk_graph *G = driver.G
    cdef fhk_solver *S = fhk_create_solver(G, gcm.mem)
    if not fhk_py_lua_callsx(driver.lua.L, driver.init, S, <void*> X):
        raise FhkError(pop(driver.lua))
    cdef GCSolver solver = GCSolver()
    solver.S = S
    solver._mem = gcm
    solver._driver = driver
    return solver

@cython.boundscheck(False)
@cython.wraparound(False)
def solve(
    GCDriver driver,
    GCSolver solver,
    list roots,
    dict subsets,
    object X,
    object result
):
    cdef CRoot root
    cdef const char *buf
    cdef int size
    cdef int i
    cdef fhk_subset ss
    cdef int16_t num[32]
    cdef void *vp[32]
    cdef int n = len(roots)
    if n > 32:
        raise FhkError(f"too many roots: {len(roots)}")
    cdef fhk_solver *S = solver.S
    cdef fhk_graph *G = fhk_py_G(S)
    for i in range(n):
        root = roots[i]
        sub = subsets.get(root.name)
        if sub is None:
            ss = fhk_py_space(S, fhk_py_var_group(G, root.idx))
            if subset_isU(ss):
                raise FhkError(f"missing space map ({root.name})")
            size = subsetIE_size(ss)
            if root.vector is None:
                if size != 1:
                    raise FhkError(f"scalar result subset not singleton: {ss}")
            else:
                num[i] = size
        else:
            # set ss, num[j] here.
            raise NotImplementedError("TODO (subset api)")
        vp[i] = fhk_setrootD(S, root.idx, ss)
    if fhk_py_lua_callsx(driver.lua.L, driver.jump, S, <void*>X) < 0:
        raise FhkError(pop(driver.lua))
    for i in range(len(roots)):
        root = roots[i]
        buf = <const char *> vp[i]
        size = fhk_py_var_size(G, root.idx)
        if root.vector:
            v = array(root.fmt, buf[:num[i]*size])
            if root.vector != array:
                v = root.vector(v)
        else:
            v = unpack(root.fmt, buf[:size])[0]
        setattr(result, root.name, v)
