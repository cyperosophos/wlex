"""Public models"""
from typing import Callable
from functools import wraps

from ..equality import Verifier

def intensionally_validated[S, T](
    func: Callable[[S], T],
    valid: Callable[[S, Verifier[object]], None],
):
    """Wraps function to (intensionally) validate argument"""
    @wraps(func)
    def wrapper(x: S, v: Verifier[object]) -> T:
        valid(x, v)
        return func(x)

    return wrapper

def validated[S, T](func: Callable[[S], T], valid: Callable[[S], None]):
    """Wraps function to validate argument"""
    @wraps(func)
    def wrapper(x: S) -> T:
        valid(x)
        return func(x)

    return wrapper

class ValidationError(ValueError):
    pass
