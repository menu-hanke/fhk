import dataclasses
import enum
import functools
import inspect
import itertools
from typing import Any, Callable, Dict, Generic, Iterable, List, Optional, Protocol, Sized, Tuple, Type, TypeVar, Union, get_args, get_origin, overload
from fhk._ctypes import CRoot, GCLua, GCPin, GCDriver, Mem, SolverState, newlua, init, isunit, ready, seq_iterss, solve, space, subsetstr
from fhk.obj import Conv, Subset, issubsettype

__all__ = (
    "root",
    "View",
    "Graph"
)

T = TypeVar("T", bound=Type)                                 # type
C = TypeVar("C", bound=Callable)                             # callable
CS = TypeVar("CS", bound=Callable[...,Subset])               # callable -> subset
S = TypeVar("S", bound=Sized)                                # sized
SS = TypeVar("SS", bound=Union[int,Callable[...,int]])       # shape

#---- c/lua interop ----------------------------------------

class ToLua(Protocol):
    def __lua__(self, lua: GCLua) -> GCPin:
        ...

class Push:
    __slots__ = "__lua__"
    def __init__(self, f: Callable[[GCLua], GCPin]):
        self.__lua__ = staticmethod(f)

LuaCallable = Union[ToLua, GCPin]

#---- python -> ctype ----------------------------------------

PY_PRIMITIVES = { float: "double", int: "int" }

def py2cts(t: Type) -> Optional[str]:
    if issubclass(t, enum.IntEnum):
        # TODO: should pick a larger type depending on values?
        return "uint8_t"
    return PY_PRIMITIVES.get(t)

#---- python <- ctype ----------------------------------------

ident = lambda x: x

class ConvScalar:
    __slots__ = "constructor", "typecode", "mem"

    def __init__(self, constructor: Callable = ident):
        self.constructor = constructor

    def init(self, typecode: str):
        self.typecode = typecode

    def set(self, mem: memoryview, ss: int):
        if not isunit(ss):
            raise ValueError(f"scalar root request non-unit subset: {subsetstr(ss)}")
        self.mem = mem[ss:]

    def get(self):
        return self.constructor(self.mem.cast(self.typecode)[0])

class ConvIter:
    __slots__ = "vector", "constructor", "typecode", "mem", "ss"

    def __init__(self, vector: Callable, constructor: Callable = ident):
        self.vector = vector
        self.constructor = constructor

    def init(self, typecode: str):
        self.typecode = typecode

    def set(self, mem: memoryview, ss: int):
        self.mem = mem
        self.ss = ss

    def get(self):
        return self.vector(map(self.constructor, seq_iterss(self.mem.cast(self.typecode), self.ss)))

#---- python callbacks ----------------------------------------

# s -> state
# i -> instance
# x -> X
def param_def(f: Callable, allow: str = "six") -> str:
    params = inspect.signature(f).parameters
    out = ""
    for p in params.values():
        if p.annotation == int:
            c = "i"
        elif p.annotation == SolverState:
            c = "s"
        elif "x" in out:
            raise TypeError(f"unexpected parameter: {p}")
        else:
            c = "x"
        if c not in allow:
            raise TypeError(f"param not valid here: {p}")
        out += c
    return out

def extract_param(state: SolverState, p: str) -> Any:
    if p == "s":
        return state
    elif p == "i":
        return state.inst
    elif p == "x":
        return state.X

def fn_wrap_params(f: Callable, allow: str = "six") -> Callable:
    pd = param_def(f, allow)
    if pd == "s":
        return f
    @functools.wraps(f)
    def w(state):
        return f(*(extract_param(state, p) for p in pd))
    return w

def vref_wrap_subset(f: Callable[..., S]) -> Callable[..., Tuple[S, int]]:
    @functools.wraps(f)
    def w(*args):
        it = f(*args)
        return it, space(len(it))
    return w

def virtual(name: str, f: Callable, cts: Optional[str] = None, copy: bool = True) -> Push:
    sig = inspect.signature(f)
    rt = sig.return_annotation
    if rt is not inspect.Signature.empty:
        orig = get_origin(rt)
        args = get_args(rt)
        # -> Tuple[..., Subset]
        if orig in (tuple, Tuple) and len(args) == 2 and issubsettype(args[1]):
            orig = get_origin(args[0])
            args = get_args(args[0])
        # -> Iterable[...] or Iterable
        elif orig and issubclass(orig, Iterable):
            f = vref_wrap_subset(f)
        if orig and issubclass(orig, Iterable):
            what = "iter"
            if (not cts) and len(args) == 1:
                cts = py2cts(args[0])
        else:
            what = "scalar"
            if not cts:
                cts = py2cts(rt)
    else:
        # could error here as well. whatever.
        # it's gonna blow up at runtime anyway if we assumed wrong.
        what = "scalar"
    f = fn_wrap_params(f)
    return Push(lambda lua: lua.fhk_py.pyvirtual(name, f, cts, what, copy)[0])

def anymap(name: str, inverse: str, f: Callable, scalar: bool = False) -> Push:
    flags = f"{'i' if 'i' in param_def(f) else 'k'}{'s' if scalar else 'v'}"
    f = fn_wrap_params(f, allow="six" if "i" in flags else "sx")
    return Push(lambda lua: lua.fhk_py.pymap(name, inverse, flags, f)[0])

def group(name: str, *rules: Any) -> Push:
    return Push(lambda lua: lua.fhk_py.rules.group(name, *rules)[0])

def label(kv: Dict[str, int]) -> Push:
    return Push(lambda lua: lua.fhk_py.rules.label(lua.fhk_py.newtab(*itertools.chain(*kv.items()))[0])[0])

def shape(s: Any) -> Push:
    if callable(s):
        s = fn_wrap_params(s, allow="sx")
    return Push(lambda lua: lua.fhk_py.shape(s)[0])

def edgerule(
    rule: str,
    map: Optional[str] = None,
    ctype: Optional[str] = None,
    scalar: Optional[bool] = None
) -> Push:
    rank = "s" if scalar is True else ("v" if scalar is False else None)
    return Push(lambda lua: lua.fhk_py.edgerule(rule, map, ctype, rank)[0])

#---- view & rules ----------------------------------------

@dataclasses.dataclass
class MapDef:
    view: "View"
    name: str
    scalar: bool
    f: Callable

    def inverse(self, name: str, scalar: bool = False) -> Callable[[CS], CS]:
        def deco(f):
            self.view.append(anymap(self.name, name, self.f, self.scalar))
            self.view.append(anymap(name, self.name, f, scalar))
            return f
        return deco

class View(list[LuaCallable]):

    def __lua__(self, lua: GCLua) -> GCPin:
        return lua.fhk_py.rules.composite(*self)[0]

    def group(self, name: str) -> "View":
        v = View()
        self.append(group(name, v))
        return v

    @overload
    def shape(self, x: str) -> Callable[[SS], SS]: ...
    @overload
    def shape(self, x: SS) -> SS: ...

    def shape(self, x):  # type: ignore
        if isinstance(x, str):
            def deco(f):
                self.append(group(x, shape(f)))
                return f
            return deco
        else:
            self.append(shape(x))
            return x

    @overload
    def given(self, x: str, ctype: Optional[str] = None, copy: bool = True) -> Callable[[C], C]: ...
    @overload
    def given(self, x: T) -> T: ...

    def given(self, x, ctype=None, copy=True):     # type: ignore
        if isinstance(x, type):
            raise NotImplementedError("TODO")
        else:
            def deco(f):
                self.append(virtual(x, f, ctype, copy))
                return f
            return deco

    @overload
    def map(self, name: str, inverse: None = None, scalar: bool = False) -> Callable[[Callable[...,Subset]], MapDef]: ...
    @overload
    def map(self, name: str, inverse: str, scalar: bool = False) -> Callable[[CS], CS]: ...

    def map(self, name, inverse=None, scalar=False): # type: ignore
        if inverse is None:
            def deco(f): # type: ignore
                return MapDef(self, name, scalar, f)
            return deco
        else:
            def deco(f): # type: ignore
                self.append(anymap(name, inverse, f, scalar))
                return f
            return deco

    def edgerule(
        self,
        rule: str,
        map: Optional[str] = None,
        ctype: Optional[str] = None,
        scalar: Optional[bool] = None
    ) -> "View":
        self.append(edgerule(rule, map, ctype, scalar))
        return self

    def label(self, *args: Dict[str, int], **kwargs: int) -> "View":
        for x in args:
            kwargs.update(x)
        self.append(label(kwargs))
        return self

#---- graph & solver ----------------------------------------

class SolverFn(Generic[T]):
    _driver: GCDriver
    _result: Type
    _roots: List[CRoot]

    def __call__(
        self,
        state: Any = None,
        solver: Optional[SolverState] = None,
        mem: Optional[Mem] = None,
        subset: Dict[str, Subset] = {}
    ) -> T:
        if solver is None:
            if mem is None:
                mem = Mem()
            solver = init(self._driver, mem, state)
        else:
            solver.X = state
        result = self._result()
        solve(self._driver, solver, self._roots, subset, result)
        return result

@dataclasses.dataclass
class Root:
    name: str
    ctype: Optional[str]

# this only exists to satisfy type checkers, ie. so that callers can do
# class Result:
#     x: float = root("a#x")
# and have it pass typecheck.
def root(name: str, ctype: Optional[str] = None) -> Any:
    return Root(name=name, ctype=ctype)

@dataclasses.dataclass
class GenRoot:
    name: str
    conv: Conv
    ref: GCPin

@dataclasses.dataclass
class GenSolver:
    fn: SolverFn
    roots: List[GenRoot]

def defsolver(lua: GCPin, state: GCPin, result: Type) -> GenSolver:
    roots = []
    for k,v in result.__dict__.items():
        if not isinstance(v, Root):
            continue
        cts = v.ctype
        if k in result.__annotations__:
            ann = result.__annotations__[k]
            orig = get_origin(ann)
            if orig:
                args = get_args(ann)
                conv = ConvIter(orig, len(args) >= 1 and args[0] or ident)
                ann = orig
            else:
                conv = ConvScalar(ann)
            if not cts:
                cts = py2cts(ann)
        else:
            conv = ConvIter(list)
        ref, = lua.setroot(state, v.name, cts)
        roots.append(GenRoot(k, conv, ref))
    fn = SolverFn()
    fn._result = result
    return GenSolver(fn, roots)

class Graph:
    _lua: GCPin
    _solvers: List[GenSolver]

    def __init__(self, *args: Union[LuaCallable, str], _lua: Optional[GCPin] = None):
        if _lua is None:
            _lua = newlua()
        self._lua = _lua
        self._solvers = []
        views, graphs = [], []
        for x in args:
            (graphs if isinstance(x, str) else views).append(x)
        self._state, = _lua.rules.newstate(View(*views))
        self.include(*graphs)

    def solver(self, result: T) -> SolverFn[T]:
        s = defsolver(self._lua, self._state, result)
        self._solvers.append(s)
        return s.fn

    def include(self, *files: str):
        self._lua.rules.read(self._state, *files)

    def __enter__(self) -> "Graph":
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.ready()

    def ready(self):
        d = ready(self._state)
        for s in self._solvers:
            fn = s.fn
            fn._driver = d
            roots = []
            for r in s.roots:
                idx, fmt = self._lua.getroot(r.ref)
                r.conv.init(fmt)
                roots.append(CRoot(name=r.name, conv=r.conv, idx=idx))
            fn._roots = roots
