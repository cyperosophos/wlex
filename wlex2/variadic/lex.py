from typing import Iterable

from ..model.category import Obj, Mor, Composition
from ..model.lex import Equalizer, Parallel, Fork as ConcreteFork, Inclusion
from ..proven import lex
from ..trusted import lex as plex
from ..equality import Verifier
#from .cart import *

Fork = plex.Fork
Lift = plex.Lift

def _complete(obj: Obj, requirements: Iterable[tuple[Mor, Mor]]):
    if isinstance(obj, Equalizer):
        reqs = set(obj.requirements)
    else:
        reqs: set[tuple[Mor, Mor]] = set()

    for req in requirements:
        if req in reqs:
            continue

        for mor in req:
            src = mor.source
            if isinstance(src, Equalizer):
                for r in src.flat_requirements():
                    if r in reqs:
                        continue

                    reqs.add(r)
                    yield r

        reqs.add(req)
        yield req

# def _complete_with_eqs(obj: Obj, requirements: Iterable[tuple[tuple[Mor, Mor], Eq[Mor]]]):
#     eq_map = dict(requirements)
#     for req in _complete(obj, eq_map):
#         yield req, eq_map[req]

def equalizer(obj: Obj, requirements: Iterable[tuple[Mor, Mor]]) -> Fork:
    # The list of requirements must be complete in the sense that any requirement of
    # a source of a requirement in the list must precede the requirement in the list.
    res = obj
    for r in _complete(obj, requirements):
        par = Parallel(res, (r,))
        res = lex.equalizer(par)
        assert isinstance(res, Equalizer)
        res.frozen = False

    if not isinstance(res, Equalizer):
        raise ValueError("Empty requirements")

    res.frozen = True
    return res

def lift(
    mor: Mor,
    #requirements: Iterable[tuple[Mor, Mor]],
    target: Obj,
    proofs: Verifier[object],
    restrict: bool = False,
) -> Lift:
    # The result can be the same morphism
    # Equalities (in `requirements`) don't change by composition with adapted handle.
    res = Lift.ensure(mor)
    mtarget = mor.target
    for r in _complete(mtarget, requirements):
        f = ConcreteFork(res.mor, (r,))
        if restrict:
            res = restricting_lift(f, proofs)
        else:
            res = lex.lift(f, proofs)

        mtarget = res.mor.target
        assert isinstance(mtarget, Equalizer)
        mtarget.frozen = False

    if not isinstance(mtarget, Equalizer):
        raise ValueError("Empty requirements")

    mtarget.frozen = True
    return res

def restricting_lift(f: Fork, proofs: Verifier[object]) -> Lift:
    try:
        # This will still fail if the superobjects don't coincide.
        return lex.lift(f, proofs)
    except lex.ProofError as pe:
        eq = pe.eq
        mor = f.handle()
        source = mor.source

        if isinstance(source, Equalizer):
            mor = mor.extend() # The original source will get reused.
            source.frozen = False

        eqr = plex.equalizer(Parallel(source, (eq,)))
        assert isinstance(eqr, Equalizer)
        mor = Composition.strict((mor, Inclusion(eqr)))
        f = ConcreteFork(mor, f.parallel())
        # Avoid superfluous check.
        return plex.lift(f)

# For now, we don't do variadic `_fork` and `lift_ihat` because there
# is no way to determine where the lift requirements start and where
# the fulfilled requirements end.

def req(obj: Obj, *requirements: tuple[AdaptingMor, AdaptingMor]):
    res = equalizer(obj, (
        (
            i(obj) if isinstance(i, Callable) else i,
            j(obj) if isinstance(j, Callable) else j,
        )
        for i, j in requirements
    ))
    assert isinstance(res, Obj)
    return res
