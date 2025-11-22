"""High level interface for cartesian ambient"""
from collections.abc import Sequence, Callable
from typing import TypeGuard

from .cells import Obj, Mor, Eq
from . import category
from .category import MorLike, all_morlike, Transformation
from .public import cart as public
from .cells.cart import Product

class Context(category.Context):
    __slots__ = ()

    terminal = Product()
    pairing = staticmethod(public.pairing)
    pairing_eq = staticmethod(public.pairing_eq)

    def el(self, name: str, cell: MorLike | None, target: Obj | None = None):
        return self.mor(name, cell, target and (self.terminal, target))

def _mor_pairing(pair: category.Composer[Mor], components: Itera):
    pass

def _pairing(
    pair: category.Composer[Mor],
    components: Sequence[MorLike | Eq],
):
    def _all_mor_or_obj(
        comps: Sequence[MorLike],
    ) -> TypeGuard[Sequence[Mor | Obj]]:
        return all(not isinstance(c, Callable) for c in comps)

    # TODO: First convert all obj to mor

    if not components:
        raise ValueError("Empty pairing is not allowed.")

    if all_morlike(components):
        if _all_mor_or_obj(components):
            # Handle case of actual span


        def _pair(source: Obj):
            return _mor_pairing()



def pairer(ctx: Context):
    pair = ctx.pairing