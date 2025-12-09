"""High level interface fo the lex ambient"""
from abc import ABCMeta

from .cells import Obj, Mor, Eq, PrimMor
from . import cart
from .cells.lex import LexObj, LexMor, LabeledParallel

class Context(cart.Context):
    """Handles cells of a theory with ambient lex"""
    __slots__ = ()

    @staticmethod
    def req(name: str | int = 0):
        """Create requirement law from name"""
        def _req(source: Obj):
            return source.req(name)

        return _req

class LexAmbientObj(LexObj):
    """Models object `lex.Obj` with requirements"""
    __slots__ = ()

    def requiring(self, first: LabeledParallel, *eqs: LabeledParallel):
        # Use the binary operation. If requirement is a law then resolve
        # against Subobject with requirements up to the previous one.
        pass

class LexAmbientMor(LexMor, metaclass=ABCMeta):
    """Models object `lex.Mor` with fulfilled requirements"""
    __slots__ = ()

    def where

class LexAmbientPrimMor(PrimMor, LexAmbientMor, metaclass=ABCMeta):
    """Models object `lex.Mor` as primitive with fulfilled requirements"""
    __slots__ = ()
