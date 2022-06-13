from typing import List, Sequence, Tuple

def ident_unannotated(x):
    return x

def ident_conv_annotated(x: int) -> float:
    return x

def dot_seq(xs: Sequence[float], ys: Sequence[float]) -> float:
    return sum(x*y for x,y in zip(xs, ys))

def sq_list(xs: List[float]) -> List[float]:
    return [x**2 for x in xs]

def multiret(xs: List[float]) -> Tuple[float, List[float]]:
    return sum(xs), xs

def errfunc():
    raise RuntimeError("something happened")

def rank_mismatch(xs: Sequence[float]) -> List[float]:
    return xs[0] # type: ignore
