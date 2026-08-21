from typing import Iterable, Collection

from ..model.category import Obj, Mor
from ..proven import lex
from ..trusted import lex as plex
from ..model.lex import Equalizer, Lift as StrictLift
from ..model.category import ProvenFork
from ..equality import El, Eq
from .cart import *

Parallel = Iterable[tuple[Mor, Mor]]
Fork = plex.Fork
Lift = plex.Lift

def proven_compose(eqs: Collection[Eq[object]]):
    def comp(c: tuple[Mor, Mor]) -> Mor:
        return compose(El(c, eqs))

    return comp

def equalizer(obj: Obj, par: El[Parallel]) -> Fork:
    # The list of requirements must be complete in the sense that any requirement of
    # a source of a requirement in the list must precede the requirement in the list.
    requirements = par.value
    inc = plex.identity(obj)
    comp = proven_compose(par.eqs)
    for req in requirements:
        i, j = req
        inc = plex.compose(( # lower
            plex.target(inc).fork(plex.compose).handle,
            inc,
        )) # TODO: Is there risk of reusing discarded Equalizer?
        sf = plex.source(inc).fork(comp)
        tf = plex.source(i).fork(comp)
        # This won't be quadratic since we are looping over the requirements of the source
        # of a requirement.
        # TODO: Fix!
        inc = lift(El(ProvenFork( # A lift without requirements is just the original morphism.
            inc,
            ((r, sf[r]) for r in tf),
        ), par.eqs)) # normalized compositions for verification of equalities?
        # TODO: Clear superfluous inclusion from requirements?
        # Use a special composition class here. The idea is that one needs to modify the
        # requirement so that it has the current equalizer as source. However, the
        # resulting equalizer will keep the original requirement.
        ef = lex.equalizer(El(
            (
                compose(El((i, inc), par.eqs)),
                compose(El((j, inc), par.eqs)),
            ),
            par.eqs,
        ))
        #!! frozen = False
        inc = ef.handle

def lift(f: El[Fork]) -> Lift:
    fk = f.value
    h = fk.handle
    #comp = proven_compose(f.eqs)
    inc = plex.identity(h.target)
    for req in fk.ordered():
        i, j = req
        # No further lift should be needed, because the requirements are in
        # an appropriate order. Only lowerings are needed (postcompositions with inclusion).
        # One can follow the approach in `equalizer` of maximally lowering then lifting.
        h = lex.lift(El(ProvenFork(
            h,
            (((
                compose(El((i, ), f.eqs)),
                compose(El((j, ), f.eqs)),
            ), fk[req]),),
        ), f.eqs))

        # The inclusion of the lift is just an inclusion from the target of the
        # lift to the source of the requirement. This lift can be trusted.
        src = plex.source(inc)
        inc = h.target.fork(plex.compose).handle
        inc = StrictLift.strict(inc, src)
