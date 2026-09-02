from typing import Iterator, Callable
from itertools import chain

from ..model.category import Obj, Mor
from ..model.cart import Product
from ..proven.category import identity

def it_with_first[T](it: Iterator[T]):
    for first in it:
        break
    else:
        return None, it

    return first, chain((first,), it)

Transform = Mor | Callable[[Obj], Mor] | str | int

def resolve(t: Transform, source: Obj):
    if isinstance(t, (str, int)):
        t = proj(t)

    if isinstance(t, Callable):
        return t(source)

    return t

def proj(label: str | int):
    if label == '':
        return identity

    def fn(src: Obj):
        if not isinstance(src, Product):
            raise ValueError('Source must be product.')

        if isinstance(label, str):
            l = src.label_to_idx(label)
        else:
            l = label

        return src.proj(l)

    return fn
