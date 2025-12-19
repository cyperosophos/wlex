"""High level interface fo the lex ambient"""
from abc import ABCMeta
from itertools import chain

from .cells import Obj, Eq, PrimMor
from . import cart
from .cells.lex import (
    LexObj, LexMor, LexComposition, LabeledParallel, Subobject, EqualizerMor,
)
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
            if isinstance(name, int):
                return source.ireq(name)

            return source.req(name)

        return _req

def _eq_to_par(eq: Eq):
    return eq.ssource, eq.starget

class LexAmbientObj(LexObj):
    """Models object `lex.Obj` with requirements"""
    __slots__ = ('ctx',)

    ctx: Context

    def __init__(self, ctx: Context):
        self.ctx = ctx

    def requiring(self, first: LabeledParallel, *eqs: LabeledParallel):
        compose_eq = self.ctx.compose_eq
        # TODO: Check that everywhere else in context methods public theory
        # functions are being used instead of cell methods. This ensures type
        # checking! Public functions are only needed with user provided args.

        inc = compose_eq((first[1], self.identity().ref())).equalizer()
        for eq in eqs:
            inc = inc.compose(compose_eq((eq[1], inc.ref())).equalizer())

        return Subobject(self, chain((first,), eqs))

LabeledFork = tuple[str, Eq, Eq] # Second `Eq` is proof.

class LexAmbientMor(LexMor, metaclass=ABCMeta):
    """Models object `lex.Mor` with fulfilled requirements"""
    __slots__ = ('ctx',)

    ctx: Context

    def __init__(self, ctx: Context):
        self.ctx = ctx

    def where(self, first: LabeledFork, *forks: LabeledFork):
        equalizer_pairing = self.ctx.equalizer_pairing
        compose_eq = self.ctx.compose_eq

        _, req, proof = first
        lift = equalizer_pairing((
            self, *_eq_to_par(req), proof,
        ))[0]
        inc = lift.target.inclusion()
        for fork in forks:
            _, req, proof = fork
            lift = equalizer_pairing((
                lift,
                # TODO: Make sure proof and req can always be compared.
                *_eq_to_par(compose_eq((req, inc.ref()))),
                proof,
            ))[0]
            inc = inc.compose(lift.target.inclusion())

        return EqualizerMor(self, Subobject(self.target, (
            (n, r) for n, r, _ in chain((first,), forks)
        )))

class LexAmbientPrimMor(PrimMor, LexAmbientMor, metaclass=ABCMeta):
    """Models object `lex.Mor` as primitive with fulfilled requirements"""
    __slots__ = ()

class LexAmbientComposition(LexComposition, LexAmbientMor):
    """Composition with fulfilled requirements"""
    __slots__ = ()

LexAmbientMor.comp_cls = LexAmbientComposition
