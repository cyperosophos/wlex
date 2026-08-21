"""Public models"""
from typing import Callable
from functools import wraps

from ..equality import Verifier

def intensional_validate[T](
    x: T, v: Verifier[object],
    valid: Callable[[T, Verifier[object]], bool],
):
    """Check that `x` passes (intensional) validation"""
    if not valid(x, v):
        raise ValueError(f"{x} is not {valid.__name__}")

def intensionally_validated[S, T](
    func: Callable[[S], T],
    valid: Callable[[S, Verifier[object]], bool],
):
    """Wraps function to (intensionally) validate argument"""
    @wraps(func)
    def wrapper(x: S, v: Verifier[object]) -> T:
        intensional_validate(x, v, valid)
        return func(x)

    return wrapper

def validate[T](x: T, valid: Callable[[T], bool]):
    """Check that `x` passes validation"""
    if not valid(x):
        raise ValueError(f"{x} is not {valid.__name__}")

def validated[S, T](func: Callable[[S], T], valid: Callable[[S], bool]):
    """Wraps function to validate argument"""
    @wraps(func)
    def wrapper(x: S) -> T:
        validate(x, valid)
        return func(x)

    return wrapper
