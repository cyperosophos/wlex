"""High level interface fo the lex ambient"""
from itertools import chain

from .cells import Obj, Mor, Eq
from . import cart
from .cells.lex import Subobject, EqualizerMor
from .category import Law, mor_like_to_mor, eq_like_to_eq
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

LabeledParallelLike = tuple[str, cart.MorLike, cart.MorLike]
LabeledForkLike = tuple[str, cart.MorLike, cart.MorLike, cart.EqLike]

def _lpl_to_lp(obj: Obj, eq: LabeledParallelLike):
    label, ssource, starget = eq
    return label, Eq(
        mor_like_to_mor(obj, ssource),
        mor_like_to_mor(obj, starget),
    )

def _lfl_to_lf(mor: Mor, fork: LabeledForkLike):
    label, ssource, starget, eq = fork
    return (
        *_lpl_to_lp(mor.target, (label, ssource, starget)),
        eq_like_to_eq(mor.source, eq),
    )

def requirer(ctx: Context):
    compose_eq = ctx.compose_eq

    # TODO: Functions like this should actually be a method of Context!
    def require(obj: Obj, first: LabeledParallelLike, *eqs: LabeledParallelLike):
        # TODO: Check that everywhere else in context methods public theory
        # functions are being used instead of cell methods. This ensures type
        # checking! Public functions are only needed with user provided args.

        first_ = _lpl_to_lp(obj, first)
        eqs_ = [_lpl_to_lp(obj, eq) for eq in eqs]
        inc = compose_eq((first_[1], obj.identity().ref())).equalizer()
        for eq in eqs_:
            inc = inc.compose(compose_eq((eq[1], inc.ref())).equalizer())

        return Subobject(obj, chain((first_,), eqs_))

    return require

LabeledFork = tuple[str, Eq, Eq] # Second `Eq` is proof.

def prover(ctx: Context):
    equalizer_pairing = ctx.equalizer_pairing
    compose_eq = ctx.compose_eq

    def prove(mor: Mor, first: LabeledForkLike, *forks: LabeledForkLike):
        first_ = _lfl_to_lf(mor, first)
        forks_ = [_lfl_to_lf(mor, fork) for fork in forks]
        _, req, proof = first_
        lift = equalizer_pairing((
            mor, *_eq_to_par(req), proof,
        ))[0]
        inc = lift.target.inclusion()
        for fork in forks_:
            _, req, proof = fork
            lift = equalizer_pairing((
                lift,
                # TODO: Make sure proof and req can always be compared.
                *_eq_to_par(compose_eq((req, inc.ref()))),
                proof,
            ))[0]
            inc = inc.compose(lift.target.inclusion())

        return EqualizerMor(mor, Subobject(mor.target, (
            (n, r) for n, r, _ in chain((first_,), forks_)
        )))

    return prove
