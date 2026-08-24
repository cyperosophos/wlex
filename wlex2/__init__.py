from typing import TypeGuard

def is_tuple(x: object) -> TypeGuard[tuple[object]]:
    return isinstance(x, tuple)
