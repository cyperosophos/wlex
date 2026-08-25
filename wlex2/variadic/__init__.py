from ..model.category import Obj, Mor
from typing import Iterator, Callable, Iterable
from itertools import chain

def it_with_first[T](it: Iterator[T]):
    for first in it:
        break
    else:
        return None, it

    return first, chain((first,), it)

AdaptingMor = Mor | Callable[[Obj], Mor]
AdaptingComposable = Iterable[AdaptingMor]