"""Private model of `lex` morphisms"""
#from typing import Iterable, TypeGuard

from ..model import lex
from .cart import *
from ..equality import Eq

Parallel = lex.BaseParallel
Fork = lex.BaseFork #tuple[Mor, Parallel, Eq[Mor]]
Lift = lex.BaseLift # Every morphism is a lift along the identity.

def parallel_i(par: Parallel) -> Mor:
    return par[0][0]

def parallel_j(par: Parallel) -> Mor:
    return par[0][1]

def eq_parallel_source(par: Parallel):
    i = source(parallel_i(par))
    assert i == source(parallel_j(par))
    return Eq(i, i)

def eq_parallel_target(par: Parallel):
    i = target(parallel_i(par))
    assert i == target(parallel_j(par))
    return Eq(i, i)

def equalizer(par: Parallel) -> Fork:
    # In variadic equalizer, composing with inclusion is what allows
    # preserving previous requirements.
    # ** At a higher level one makes sure that requirements of the source of requirements
    # are always present, so that composing the inclusion or a lifting/lowering of the inclusion
    # is always possible.
    # The target of the inclusion is the the source of the previous inclusion
    # (i.e. the last state of the equalizer).
    # The variadic fork consists of a morphism, equalities and requirements
    # (hence an equalizer). The fork maps requirements to proofs.
    # Just like in the case of the equalizer, the requirements for lifting a morphism
    # need not have the target of the morphism as their source, but instead a subset
    # of such target. So it makes sense for the target of the morphism to not be
    # an equalizer.
    # On the other hand the inclusion returned here should have a target that is the
    # source of the requirement. One approach here is to allow non-flat equalizers,
    # but this seems unnecessarily complicated. We use instead a Fork class
    # (from which perhaps Equalizer inherits).
    # The goal of composing with the inclusion is to have a requirement whose source
    # is the current equalizer state. The problem of doing this is that the requirements
    # will then not be the original ones.
    # Clear requirements of superfluous inclusions (fi=gi becomes f=g). Handle this in variadic equalizer.
    #inc = lex.Inclusion(_equalizer(par))
    #i, j = par
    #return inc, par, Eq(compose((i, inc)), compose((j, inc)))
    # Use InclusionComposition class that simply changes the source? Analogous to Lift.
    #src = par.source
    return lex.Equalizer(par)

    # `inc` is an intensional identity in case of a tautological requirement.
    #ef = eqr.fork(compose)
    #inc = lex.Lift.strict(ef.handle, src)
    # We pass equalities to Fork init since they need to be type-checked in `proven`,
    # their origin is not to be trusted.
    # NOTE: An inclusion is a restriction of the identity!!
    # The inclusion will not be accessible when the source of `par` is a
    # non frozen equalizer, and that's fine. `par` is discarded.
    # We can still recover it from the equalizer, by removing i, j corresponding to `par`,
    # But this can't be done after the equalizer is itself discarded.
    #return RequirementFork()
    #return category.TrustedFork(inc, (par,), compose)

def equalizer_hat(par: Parallel):
    assert par == equalizer(par).parallel()
    return Eq(par, par)

def lift(f: Fork) -> Lift:
    # TODO: Must always check that the length of the parallel is the correct one (i.e. 1).
    #       Check this in `proven`. Same with other sized types.
    # The fork has one parallel and so should the lift.
    # Fork has a named parameter corresponding to an intensional equality.
    # This equality can't be extensional, since then it would be too strong
    # to get an object that's big enough. This equality has to be proven
    # using intensional equalities (equalities that appear in the actual
    # program and not in the theory of programs).
    eqr = lex.Equalizer(f.parallel())
    res = Lift.ensure(lex.Lift.strict(f.handle(), eqr))
    assert len(res) == 1
    return res

def _fork(l: Lift) -> Fork:
    # def _is_len_2(x: Eq[tuple[Mor, ...]]) -> TypeGuard[Eq[tuple[Mor, Mor]]]:
    #     return len(x.s) == len(x.t) == 2

    # def _gen_eq(eq_it: Iterable[Eq[Mor]]):
    #     for e in eq_it:
    #         d = Eq[Mor].from_tuple(e, mor)
    #         assert _is_len_2(d)
    #         yield d.apply(compose)

    mor = l.mor
    par = l.parallel()
    ef = equalizer(par)
    # Having been able to construct the lift means that the equalities are already registered.
    return lex.ProvenFork(
        compose((ef.handle(), mor)),
        par,
    #    _gen_eq(ef.eq()),
    )

def lift_hat(f: Fork):
    assert Fork.__eq__(f, _fork(lift(f)))
    return Eq(f, f)

def lift_ihat(l: Lift):
    return Eq(l, lift(_fork(l)))
