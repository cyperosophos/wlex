"""High level interface fo the lex ambient"""
from abc import ABCMeta

from .cells import Obj, Mor, Eq, PrimMor
from . import cart
from .cells.lex import LexObj, LexMor, LexComposition, LabeledParallel
from .category import Law
from .public import lex as public

class Context(cart.Context):
    """Handles cells of a theory with ambient lex"""
    __slots__ = ()

    equalizer = staticmethod(public.equalizer)
    equalizer_pairing = staticmethod(public.equalizer_pairing)
    equalizer_pairing_unique = staticmethod(public.equalizer_pairing_unique)

    @staticmethod
    def req(name: str | int = 0):
        """Create requirement law from name"""
        @Law
        def _req(source: Obj):
            return source.req(name)

        return _req

class LexAmbientObj(LexObj):
    """Models object `lex.Obj` with requirements"""
    __slots__ = ('ctx',)

    def __init__(self, ctx: Context):
        self.ctx = ctx

    def requiring(self, first: LabeledParallel, *eqs: LabeledParallel):
        # Use the binary operation. If requirement is a law then resolve
        # against Subobject with requirements up to the previous one.
        equalizer = self.ctx.equalizer



class LexAmbientMor(LexMor, metaclass=ABCMeta):
    """Models object `lex.Mor` with fulfilled requirements"""
    __slots__ = ()

    def where(self):
        pass

class LexAmbientPrimMor(PrimMor, LexAmbientMor, metaclass=ABCMeta):
    """Models object `lex.Mor` as primitive with fulfilled requirements"""
    __slots__ = ()

class LexAmbientComposition(LexComposition, LexAmbientMor):
    """Composition with fulfilled requirements"""
    __slots__ = ()

LexAmbientMor.comp_cls = LexAmbientComposition
