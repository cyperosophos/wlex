from typing import Iterator
from itertools import chain

def it_with_first[T](it: Iterator[T]):
    for first in it:
        break
    else:
        return None, it

    return first, chain((first,), it)