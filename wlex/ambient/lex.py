from ..theory.lex import Lex as BLex
from ..ambient import Obj, Mor, Eq
from .category import Category, variadic, Polymor

class Error(Exception):
    pass

class Pair:
    pass

class Pairer:
    @classmethod
    def pair(
        cls,
        p: Mor | Polymor | Eq | Obj,
        q: Mor | Polymor | Eq | Obj,
    ) -> Mor | Polymor | Eq:
        p, q = (
            Category.identity(m) if isinstance(m, Obj) else m
            for m in (p, q)
        )

        if isinstance(q, Polymor):
            if isinstance(p, Eq):
                raise Error
        return UnsourcedPair(p, q)

class Lex(Category):
    def pair():
        pass