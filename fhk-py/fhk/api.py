import dataclasses
import enum
import inspect
from typing import Any, Callable, Dict, Generic, List, Optional, Sequence, Tuple, Type, TypeVar, Union, get_args, get_origin, overload
from fhk._ctypes import LuaState, Mem, Pin
from fhk.obj import Subset, issubsettype

__all__ = ("Graph", "View", "root")

T = TypeVar("T", bound=Type)                                 # type
C = TypeVar("C", bound=Callable)                             # callable
CS = TypeVar("CS", bound=Callable[...,Subset])               # callable -> subset
SS = TypeVar("SS", bound=Union[int,Callable[...,int]])       # shape

#---- api types ----------------------------------------
# keep in sync with fhk_py.lua!

@dataclasses.dataclass
class XComposite:
    rules: List[Any]
    what: str = "composite"

@dataclasses.dataclass
class XGroup:
    name: str
    rule: Any
    what: str = "group"

@dataclasses.dataclass
class XNamed:
    name: str
    rule: Any
    what: str = "named"

@dataclasses.dataclass
class XGivenFunc:
    func: Callable
    subset: bool
    params: str
    desc: str
    type: Optional[Type]
    ctype: Optional[str]
    vector: Optional[Type]
    what: str = "given(func)"

@dataclasses.dataclass
class XMapFunc:
    func: Callable
    params: str
    desc: str
    inverse: str
    flags: str
    what: str = "map(func)"

@dataclasses.dataclass
class XShapeFunc:
    func: Callable
    params: str
    what: str = "shape(func)"

@dataclasses.dataclass
class XShapeNum:
    shape: int
    what: str = "shape(num)"

@dataclasses.dataclass
class XLabel:
    labels: Dict[str, int]
    what: str = "label"

@dataclasses.dataclass
class XEdgeRule:
    rule: str
    map: Optional[str]
    cts: Optional[str]
    rank: Optional[str]
    what: str = "edgerule"

XRule = Union [
    XComposite,
    XGroup,
    XNamed,
    XGivenFunc,
    XMapFunc,
    XShapeFunc,
    XShapeNum,
    XLabel,
    XEdgeRule
]

@dataclasses.dataclass
class XRoot:
    attr: str
    var: str
    ctype: Optional[str]
    constructor: Optional[Callable]
    vector: Optional[Callable]

def describe(x: Any) -> str:
    if hasattr(x, "__code__"):
        x = x.__code__
    if hasattr(x, "co_name"):
        return f"{x.co_name} ({x.co_filename}:{x.co_firstlineno})"
    else:
        return str(x)

def jparm(f: Callable) -> str:
    out = ""
    for p in inspect.signature(f).parameters.values():
        if p.annotation == int:
            out += "i"
        elif "x" not in out:
            out += "x"
    return out

def ctoverride(t: Type) -> Optional[str]:
    if issubclass(t, enum.IntEnum):
        # TODO: should pick a larger type depending on values?
        return "uint8_t"
    # primitives are handled in lua

def gfunc(f: Callable, ctype: Optional[str] = None) -> XGivenFunc:
    rt = inspect.signature(f).return_annotation
    subset = False
    vector = None
    if rt is not inspect.Signature.empty:
        orig = get_origin(rt)
        if orig and issubclass(orig, Tuple):
            args = get_args(orig)
            if len(args) != 2:
                raise TypeError(f"return tuple size mismatch: {len(args)}")
            if not issubsettype(args[1]):
                raise TypeError("second return value must be a subset type")
            subset = True
            rt = args[0]
            orig = get_origin(rt)
        if orig is not None:
            if not issubclass(orig, Sequence):
                raise TypeError(f"unrepresentable return type: {rt}")
            vector = orig
            args = get_args(rt)
            rt = args[0] if len(args) > 0 else None
        if ctype is None and rt is not None:
            ctype = ctoverride(rt)
    return XGivenFunc(
        func = f,
        subset = subset,
        params = jparm(f),
        desc = describe(f),
        type = rt,
        ctype = ctype,
        vector = vector
    )

def mapfunc(f: Callable, inverse: str, scalar: bool) -> XMapFunc:
    params = jparm(f)
    return XMapFunc(
        func = f,
        params = params,
        desc = describe(f),
        inverse = inverse,
        flags = f"{'i' if 'i' in params else 'k'}{'s' if scalar else 'v'}"
    )

@dataclasses.dataclass
class MapDef:
    view: "View"
    name: str
    scalar: bool
    f: Callable

    def inverse(self, name: str, scalar: bool = False) -> Callable[[CS], CS]:
        def deco(f):
            self.view.append(XNamed(self.name, mapfunc(self.f, name, self.scalar)))
            self.view.append(XNamed(name, mapfunc(f, self.name, scalar)))
            return f
        return deco

class View(list):

    def group(self, name: str) -> "View":
        v = View()
        self.append(XGroup(name=name, rule=XComposite(v)))
        return v

    @overload
    def shape(self, x: str) -> Callable[[SS], SS]: ...
    @overload
    def shape(self, x: SS) -> SS: ...

    def shape(self, x): # type: ignore
        if isinstance(x, str):
            return self.group(x).shape
        elif isinstance(x, int):
            self.append(XShapeNum(x))
        else:
            self.append(XShapeFunc(func=x, params=jparm(x)))
        return x

    @overload
    def given(self, x: str, ctype: Optional[str] = None) -> Callable[[C], C]: ...
    @overload
    def given(self, x: T) -> T: ...

    def given(self, x, ctype=None): # type: ignore
        if isinstance(x, type):
            raise NotImplementedError("TODO")
        else:
            def deco(f):
                self.append(XNamed(x, gfunc(f, ctype)))
                return f
            return deco

    @overload
    def map(self, name: str, inverse: None = None, scalar: bool = False) -> Callable[[Callable[...,Subset]], MapDef]: ...
    @overload
    def map(self, name: str, inverse: str, scalar: bool = False) -> Callable[[CS], CS]: ...

    def map(self, name, inverse=None, scalar=False):  # type: ignore
        if inverse is None:
            def deco(f):  # type: ignore
                return MapDef(self, name, scalar, f)
        else:
            def deco(f):  # type: ignore
                self.append(XNamed(name, mapfunc(f, inverse, scalar)))
        return deco

    def edgerule(
        self,
        rule: str,
        map: Optional[str] = None,
        ctype: Optional[str] = None,
        scalar: Optional[bool] = None
    ) -> "View":
        self.append(XEdgeRule(
            rule = rule,
            map = map,
            cts = ctype,
            rank='s' if scalar is True else ('v' if scalar is False else None)
        ))
        return self

    def label(self, *args: Dict[str, int], **kwargs: int) -> "View":
        for x in args:
            kwargs.update(x)
        self.append(XLabel(kwargs))
        return self

Rule = Union[View, XRule]

def torule(rules: List[Rule]) -> XRule:
    if len(rules) == 1 and not isinstance(rules[0], list):
        return rules[0]
    return XComposite([torule(r) if isinstance(r, list) else r for r in rules])

@dataclasses.dataclass(slots=True)
class Solver:
    _S: Pin
    _mem: Mem # <- this reference is here just to prevent gc

class SolverFn(Generic[T]):
    _lua: LuaState
    _init: Pin
    _fn: Pin
    _result: Type

    def __call__(
        self,
        state: Any = None,
        solver: Optional[Solver] = None,
        mem: Optional[Mem] = None,
        subset: Dict[str, Subset] = {}
    ) -> T:
        if solver is None:
            if mem is None:
                mem = Mem()
            solver = Solver(self._lua.callinit(self._init, mem, state), mem)
        result = self._result()
        self._lua.callsolver(self._fn, solver._S, state, result, subset)
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

def toroots(result: Type) -> List[XRoot]:
    roots = []
    # access __annotations__ here to make sure __dict__ contains it before we start iterating.
    getattr(result, "__annotations__")
    for k,v in result.__dict__.items():
        if not isinstance(v, Root):
            continue
        constructor, vector = None, None
        if k in result.__annotations__:
            ann = result.__annotations__[k]
            orig = get_origin(ann)
            if orig:
                args = get_args(ann)
                if len(args) == 1:
                    vector = orig
                    ann = args[0]
            constructor = ann
        roots.append(XRoot(attr=k, var=v.name, ctype=v.ctype, constructor=constructor, vector=vector))
    return roots

class Graph:
    _lua: LuaState
    _ref: int
    _solvers: List[Tuple[SolverFn, int]]

    def __init__(self, *args: Union[Rule, str], lua: Optional[LuaState] = None):
        self._solvers = []
        if lua is None:
            lua = LuaState()
        self._lua = lua
        self._ref = self._lua.new(torule([a for a in args if not isinstance(a, str)]))
        self.include(*(a for a in args if isinstance(a, str)))

    def solver(self, result: T) -> SolverFn[T]:
        fn = SolverFn()
        fn._lua = self._lua
        fn._result = result
        self._solvers.append((fn, self._lua.solver(self._ref, toroots(result))))
        return fn

    def include(self, *files: str):
        for f in files:
            self._lua.read(self._ref, f)

    def ready(self):
        init = self._lua.ready(self._ref)
        for s, idx in self._solvers:
            fn = self._lua.pinsolver(self._ref, idx)
            s._init = init
            s._fn = fn
        self._lua.unref(self._ref)
        # prevent any further (accidental) calls.
        setattr(self, "_lua", None)

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        self.ready()
