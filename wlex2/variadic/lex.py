from typing import Collection, Iterable

from ..model.category import Obj, Mor
from ..model.lex import Equalizer, Parallel, Fork as ConcreteFork
from ..proven import lex
from ..trusted import lex as plex
from ..equality import Verifier
from . import Transform, resolve
from .cart import product

Fork = plex.Fork
Lift = plex.Lift

def _complete(obj: Obj, requirements: Iterable[tuple[Mor, Mor]]):
    if isinstance(obj, Equalizer):
        reqs = set(obj.requirements)
    else:
        reqs: set[tuple[Mor, Mor]] = set()

    for req in requirements:
        if req in reqs:
            # No redundant requirements up to extending.
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

def equalizer(obj: Obj, requirements: Iterable[tuple[Mor, Mor]]) -> Equalizer:
    # The list of requirements must be complete in the sense that any requirement of
    # a source of a requirement in the list must precede the requirement in the list.
    res = obj
    for req in _complete(obj, requirements):
        par = Parallel(res, (req,))
        res = lex.equalizer(par)
        res.frozen = False

    if not isinstance(res, Equalizer):
        raise ValueError("Empty requirements")

    res.frozen = True
    return res

def lift(
    mor: Mor,
    target: Equalizer,
    proofs: Verifier[object],
    #restrict: bool = True,
    #fit: Callable[[Mor, tuple[Mor, Mor]], Mor],
) -> Lift:
    # The result can be the original morphism when target has no requirements.
    # In this case we must directly check that the target coincides, since we
    # wouldn't be able to do this using the binary lift.
    # Equalities (in `requirements`) don't change by composition with adapted handle.
    # For simplicity we don't check that the result ends up having `target` as target,
    # we let `compose` take care of this.
    res = mor
    mtarget = mor.target

    if isinstance(mtarget, Equalizer):
        reqs = mtarget.requirements
    else:
        reqs: Collection[tuple[Mor, Mor]] = frozenset()

    # No redundant requirements in target, assuming it came from `variadic.equalizer`.
    # On the other hand requirements in the target of mor get excluded to avoid
    # having them end up as redundant requirements in the target of the result.
    for req in target.flat_requirements():
        if req in reqs:
            continue

        f = ConcreteFork(res, (req,))
        try:
            res = lex.lift(f, proofs)
        except lex.ProofError as pe:
            eq = pe.eq
            msource = res.source
            eqr = plex.equalizer(Parallel(msource, (eq,)))
            eqr.frozen = False
            res = eqr.restrict(res)
            f = ConcreteFork(res, (req,))
            res = plex.lift(f)

        mtarget = res.target
        assert isinstance(mtarget, Equalizer)
        mtarget.frozen = False

        msource = res.source
        if isinstance(msource, Equalizer):
            msource.frozen = False

    assert isinstance(mtarget, Equalizer) and mtarget == target
    mtarget.frozen = True
    return res

# def restricting_lift(f: Fork, proofs: Verifier[object]) -> Lift:
#     try:
#         # This will still fail if the superobjects don't coincide.
#         return lex.lift(f, proofs)
#     except lex.ProofError as pe:
#         eq = pe.eq
#         mor = f.handle()
#         source = mor.source

#         if isinstance(source, Equalizer):
#             mor = mor.extend() # The original source may get reused.
#             source.frozen = False

#         eqr = plex.equalizer(Parallel(source, (eq,)))
#         assert isinstance(eqr, Equalizer)
#         mor = Composition.strict((mor, Inclusion(eqr)))
#         f = ConcreteFork(mor, f.parallel())
#         # Avoid superfluous check.
#         return plex.lift(f)

# For now, we don't do variadic `_fork` and `lift_ihat` because there
# is no way to determine where the lift requirements start and where
# the fulfilled requirements end.

def limit(
    obj: Obj | tuple[tuple[str, Obj] | Obj, ...],
    *requirements: tuple[Transform, Transform],
):
    if isinstance(obj, tuple):
        obj = product(obj)

    if not requirements:
        return obj

    return equalizer(obj, (
        (resolve(i, obj), resolve(j, obj))
        for i, j in requirements
    ))
