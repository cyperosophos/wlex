"""Public models"""
from typing import Callable

def validate[T](x: T, valid: Callable[[T], bool]):
    """Check that `x` passes validation"""
    if not valid(x):
        raise ValueError(f"{x} is not {valid.__name__}")
