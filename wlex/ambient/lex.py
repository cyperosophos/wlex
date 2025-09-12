from ..theory.lex import Lex as BLex
from ..ambient import Obj, Mor, Eq
from .category import Category, variadic, Unsourced

class Error(Exception):
    pass

class Pair:
    pass

class Pairer:
    @classmethod
    def pair(
        cls,
        p: Mor | Unsourced | Eq | Obj,
        q: Mor | Unsourced | Eq | Obj,
    ) -> Mor | Unsourced | Eq:
        p, q = (
            Category.identity(m) if isinstance(m, Obj) else m
            for m in (p, q)
        )

        if isinstance(q, Unsourced):
            if isinstance(p, Eq):
                raise Error
        return UnsourcedPair(p, q)

class Lex(Category):
    def pair():
        pass