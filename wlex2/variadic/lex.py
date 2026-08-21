from typing import Iterable

from ..model.category import Obj, Mor
from ..model.lex import Equalizer, Parallel, ProvenFork
from ..proven import lex
from ..trusted import lex as plex
from ..equality import Verifier
from .cart import *

Fork = plex.Fork
Lift = plex.Lift

def _extended(requirements: Iterable[tuple[Mor, Mor]]):
    for i, j in requirements:
        yield i.extend(), j.extend()

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
    for req in _complete(obj, _extended(requirements)):
        par = Parallel(res, (req,))
        res = lex.equalizer(par)
        assert isinstance(res, Equalizer)
        res.frozen = False

    if not isinstance(res, Equalizer):
        raise ValueError("Empty requirements")

    res.frozen = True
    return res

def lift(
    mor: Mor,
    #requirements: Iterable[tuple[tuple[Mor, Mor], Eq[Mor]]],
    requirements: Iterable[tuple[Mor, Mor]],
    proofs: Verifier[object],
) -> Lift:
    # Equalities (in `requirements`) don't change by composition with adapted handle.
    res = Lift.ensure(mor)
    tgt = mor.target
    for req in _complete(tgt, _extended(requirements)):
        par = Parallel(tgt, (req,))
        f = ProvenFork(res.mor, par)
        res = lex.lift(f, proofs)
        tgt = res.mor.target
        assert isinstance(tgt, Equalizer)
        tgt.frozen = False

    if not isinstance(tgt, Equalizer):
        raise ValueError("Empty requirements")

    tgt.frozen = True
    return res

# For now, we don't do variadic `_fork` and `lift_ihat` because there
# is no way to determine where the lift requirements start and where
# the fulfilled requirements end.
