"""Public models"""
from typing import Callable
from functools import wraps

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
