"""Private model of `lex` morphisms"""
from ..model import lex
from ..model.category import Mor
from .category import source, target, compose
from ..equality import Eq

Parallel = lex.Parallel

def parallel_i(par: Parallel) -> Mor:
    return par.i()

def parallel_j(par: Parallel) -> Mor:
    return par.j()

def eq_parallel_source(par: Parallel):
    i = source(parallel_i(par))
    assert i == source(parallel_j(par))
    return Eq(i, i)

def eq_parallel_target(par: Parallel):
    i = target(parallel_i(par))
    assert i == target(parallel_j(par))
    return Eq(i, i)

Fork = lex.BaseFork
equalizer = lex.Equalizer
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
    #return lex.Equalizer(par)

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
    assert par == equalizer(par).par
    return Eq(par, par)

Lift = Mor
lift = lex.Lift.strict

# def lift(f: Fork) -> Lift:
#     # TODO: Must always check that the length of the parallel is the correct one (i.e. 1).
#     #       Check this in `proven`. Same with other sized types.
#     # The fork has one parallel and so should the lift.
#     # Fork has a named parameter corresponding to an intensional equality.
#     # This equality can't be extensional, since then it would be too strong
#     # to get an object that's big enough. This equality has to be proven
#     # using intensional equalities (equalities that appear in the actual
#     # program and not in the theory of programs).

#     # IMPORTANT If the parallel is tautological because of the equalizer source,
#     # the equalizer here will be the source (with a redundant requirement), and
#     # the result will be *equal* to f.handle(), which might of course just be a simple morphism.
#     # Notice the inefficient `==` in Lift.strict.
#     # Having f.handle() now pointing to a reused Equalizer is not a problem because
#     # this only affects instances of Lift, and it is their `sup` mor which end up becoming
#     # the `sup` of the returned Lift. However this will be a problem if we return f.handle()
#     # itself. In fact, the `==` comparison will fail due to the target of f.handle() having being
#     # reused.
#     eqr = equalizer(f.parallel())
#     return lex.Lift.strict(f.mor(), eqr)

def _fork(l: Lift) -> Fork:
    mor = l
    t = mor.target
    assert isinstance(t, lex.Equalizer)
    eqr = equalizer(t.par)
    return lex.Fork(
        compose((eqr.mor(), mor)),
        t.par,
    )

def lift_hat(f: Fork):
    assert f == _fork(lift(f))
    return Eq(f, f)

def lift_ihat(l: Lift):
    return Eq(l, lift(_fork(l)))
