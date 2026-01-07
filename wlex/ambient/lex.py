"""High level interface fo the lex ambient"""
from itertools import chain

from .cells import Obj, Mor, Eq
from . import cart
from .cells.lex import Subobject, EqualizerMor
from .category import Law, mor_like_to_mor, eq_like_to_eq
from .public import lex as public

# TODO: Both product and pairing have to be overridden so that they
# handle subobjects. In the future coproducts will also have to be taken
# care of. In the case of pairings, when the components are equalizer
# pairings, one uses instead the supermorphism and then wraps the pairing
# in an equalizer pairing.

class Context(cart.Context):
    """Handles cells of a theory with ambient lex"""
    __slots__ = ()

    equalizer = staticmethod(public.equalizer)
    equalizer_pairing = staticmethod(public.equalizer_pairing)
    equalizer_pairing_unique = staticmethod(public.equalizer_pairing_unique)

    # TODO: Override obj so that all requirement equalities get registered.

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
        # TODO: There has to be a `prove` function which handles MorLike and
        # a simpler function which is not directly used in the theory, but used
        # during inferred lifting. Lifting is the alternative to conversion.
        # The right way to access equalities is through their signature.
        # This simplifies a lot of code. Laws can be kept even with this approach?
        # Equalities can be named but need not to.
        # Hat and requirement equalities can be accessed through refs from
        # morphisms and subobjects respectively. These are created dynamically.
        # All proven equalities appear in a global set. Subobjects need a set
        # of (parallel pairs) requirements for comparison purposes.
        # Equality instances are setoid signatures.
        # One does not know whether to apply conversion or lifiting first,
        # and more generally where to parenthize the lifted morphism.
        # One possible approach is then to parenthize maximally
        # (and to convert before lifting which should have the same effect as lifting before converting).
        # In this case one needs to try out all tails of the composition until
        # finding one that corresponds to an equality.
        # Evident requirement: the empty tail must also be tried out, it corresponds
        # to a requirement that is always fulfilled.
        # Conversion with lifting can include more than one conversion and more than one lifting.
        # The solution is to explicitly induce the conversion through composition
        # with identity. Lifting may also be required when adapting to signature target.
        # Recall that a disjoint union of subobjects is a subobject of a disjoint union.
        # A problem arises with having to replicate a subobject (which may be
        # also a product or disjoin union). The solution (which may fail) is to
        # normalize aggressively, make subobject products into subobjects, etc.
        # The way to normalize subobject disjoint unions seems to involve disjoint
        # union of morphisms. Operations such as projections must still be applicable
        # to the product-turned-subobject, especially for the purpose of composition normalization.
        # A pullback must have projections without having to be converted into a product.
        # There must be then a ProductSubobject class and eventually also
        # a CoproductSubobject class (Initial algebra subobject?).

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
