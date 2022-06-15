from typing import Iterable, Type, Union

__all__ = (
    "Subset",
    "EMPTYSET"
)

Subset = Union[int, Iterable[int]]
EMPTYSET = -1

def issubsettype(t: Type) -> bool:
    return t == Subset or issubclass(t, (int, Iterable))
