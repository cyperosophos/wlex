from typing import Mapping, Collection, Iterable, Iterator
from abc import ABCMeta
from itertools import chain

from ..model.category import Obj, Mor
from ..proven import lex
from ..trusted import lex as plex
from ..model.lex import Equalizer, Lift, Inclusion
from ..equality import El, Eq
from .cart import *

Parallel = tuple[Obj, Collection[tuple[Mor, Mor]]]

def _flat_lift(mor: Mor, tgt: Obj):
    if mor.target == target:
        return mor

    # In theory we may still obtain an intensional identity when
    # mor.target and target are intensionally equal.
    return Lift(mor, tgt)

class Fork(Mapping[tuple[Mor, Mor], Eq[Mor]], metaclass=ABCMeta):
    __slots__ = ('handle',)
    handle: Mor

    def __init__(self, handle: Mor):
        self.handle = handle

class InclusionFork(Fork):
    __slots__ = ('_source', '_eqs')
    _source: Equalizer
    _eqs: Collection[Eq[object]]

    def __init__(self, handle: Mor, eqs: Collection[Eq[object]]):
        super().__init__(handle)
        src = handle.source
        assert isinstance(src, Equalizer)
        self._source = src
        self._eqs = eqs #!!

    def __getitem__(self, req: tuple[Mor, Mor]):
        if req not in self._source.requirements:
            raise KeyError("Not a requirement")

        i, j = req

        # We use high level compose so that factors get flattened.
        # These are exactlty the equalities needed for lifting the fork,
        # which results in an intensional identity.
        # We follow a kind of "gradual lifting" by starting from the longest
        # arrows (the morphism with the largest targets).
        # The general fork has a handle morphism. The target of the handle may
        # be larger than the source of (some of the) requirements.
        # We then lift it as needed so that its target matches each individual
        # fork (by first lifting the forks with the largest target) until we've
        # lifted all forks.
        return Eq(
            compose(El((i, _flat_lift(self.handle, plex.source(i))), self._eqs)),
            compose(El((j, _flat_lift(self.handle, plex.source(j))), self._eqs)),
        )

    def __iter__(self):
        return iter(self._source.requirements)

    def __len__(self):
        return len(self._source.requirements)

class DictFork(Fork):
    __slots__ = ('_map',)
    _map: dict[tuple[Mor, Mor], Eq[Mor]]

    def __init__(self, handle: Mor, map_: dict[tuple[Mor, Mor], Eq[Mor]]):
        super().__init__(handle)
        self._map = map_

    def __iter__(self):
        return iter(self._map)

    def __len__(self):
        return len(self._map)

    def __getitem__(self, req: tuple[Mor, Mor]):
        return self._map[req]

# Normalizing here means using the common superobject (which will not be an Equalizer).
# The resulting equalizer must be a subobject of all sources. Hence, it must have the
# requirements of those sources.

def _all_requirements(sup: Obj, requirements: Iterable[tuple[Mor, Mor]]) -> Iterator[tuple[Mor, Mor]]:
    reqs: set[tuple[Mor, Mor]] = set()
    for req in requirements:
        if req in reqs:
            continue

        i, j = req
        if plex.target(i) != plex.target(j):
            raise ValueError("Targets must be the same on sides of requirement.")

        for r in req:
            # The two sides of the requirement need not have the same requirements.
            src = plex.source(r)
            if isinstance(src, Equalizer):
                if sup != src.sup:
                    raise ValueError(f"Source of requirement must have {sup} as superobject.")

                for r in src.requirements:
                    # We assume `src.requirements are complete`.
                    if r not in reqs:
                        reqs.add(r)
                        yield r
            elif sup != src:
                raise ValueError("Source of requirement must be superobject.")

        reqs.add(req)
        yield req

def _equalizer(obj: Obj, requirements: Iterable[tuple[Mor, Mor]]):
    if isinstance(obj, Equalizer):
        sup = obj.sup
        assert not isinstance(sup, Equalizer) # Only support flat equalizer
        # The requirements of obj are not used during type-check, even if this
        # means the resulting equalizer will end up having redundant requirements.
        preqs = obj.requirements
    else:
        sup = obj
        preqs = ()

    # Can end up being larger than `requirements`
    oreqs = _all_requirements(sup, requirements)
    return Equalizer(sup, frozenset(chain(preqs, oreqs)))

def equalizer(par: Parallel) -> Fork:
    # Ad hoc type-checking. Therefore no `El`.
    # Ultimately the question is not whether one builds variadic based on binary,
    # especially since the data structure differ by the flattening (cf composition),
    # but whether the construction satisfies conditions, the proofs of which for now need
    # not be written in code.
    # It would be better if binary could be used to build variadic (e.g. by using mutability).
    # One would then have extentional monoidality of composition, (index) product and pairing,
    # (commutative monoidality) equalizers and lifts.

    # At a higher level tautological requirements must be removed.
    # Requirements are not ordered, in the sense the inclusion relation generated
    # by the requirements of their sources need not be a total order.
    # The requirement must already satisfy the parallel condition.
    # We apply public.equalizer for type checking in a way that the
    # result is the (non-normalized) equalizer. Each requirement has
    # to be precomposed as needed with the previous inclusion (said
    # otherwise, the source must be adapted to the smaller subobject).
    # Also if the equalizer is missing requirements for the source of the
    # the new requirement, then these missing requirements must be added.
    # The target of each inclusion is just the original source of the
    # requirement, so that each fork is by itself not an equalizer fork.

    # The set of requirements is already straightened before being passed
    # as an argument to this function. Requirements must then actually need
    # to be ordered. The resulting fork must reflect this order for the sake of the hat.

    obj, requirements = par.value
    eqr, oreqs = _equalizer(obj, requirements)
    inc = plex.identity(obj)

    # for i, j in oreqs:
    #     # Lift the inclusion as needed. Here, the superobject of the inclusion
    #     # may be an equalizer. Lifting is needed when the source of the requirement
    #     # is an equalizer. After composing with the lifted inclusion the source of the
    #     # requirement is the equalizer in its current state.
    #     # We know that lifting passes type-checking as long as superobjects match.
    #     # Since the source of a requirement can also be larger than the target of
    #     # the prev inclusion, the more general approach is to enlarge the target of
    #     # the inclusion before lifting.

    #     inc_t = plex.target(inc)
    #     if isinstance(inc_t, Equalizer):
    #         # One has to use composition because the source (equalizer) of
    #         # inc is not flat.
    #         inc = plex.compose((Inclusion(inc_t), inc))

    #     i_inc = plex.compose((i, Lift(inc, plex.source(i))))
    #     j_inc = plex.compose((j, Lift(inc, plex.source(j))))
    #     inc, _, _ = lex.equalizer(El((i_inc, j_inc), par.eqs))

    # The returned equalizer does not have the same requirements as the "bumpy"
    # equalizer, it does not even have the same equalities because of the way
    # "bumpy" inclusions are constructed.
    return InclusionFork(Inclusion(eqr), par.eqs)

    # There are a few possibilities:
    # - The (sub)requirement is/is not in reqs.
    # - It was in reqs and now is in the requirement of the source
    #   of the inclusion, in which case the inclusion can be lifted.

    # There is no danger of tautological ...
    # The equalizer resulting from this always has only one requirement
    # with the superobject having the remaining requirements.

    # There are a few possibilities about the inclusion:
    # - The next requirement has the target of the inclusion as its source.
    # - The next requirement has a source with requirements among the already
    #   processed requirements. In this case one must lift!
    #   If lifting is not possible due to missing requirements in the source of
    #   inc (the "partial" equalizer), then just make sure these requirements
    #   appear in `par.value`.
    # The existence of the inclusion is given in the same way as the existence
    # of (multi-component) projections. For each requirement there is an inclusion
    # that takes it away. There there are the compositions of such inclusions
    # (analogous to the pairing of the projections).
    # If one refines the analogy with projections, then the actual inclusions
    # to be considered as fundamental are the ones that remove all requirements
    # until all that remains is the original source of the requirement corresponding
    # to the inclusion. All other inclusions are obtained by lifting.

    # Have one inclusion per requirement. The source of all inclusions
    # is the equalizer.

def lift(f: El[Fork]) -> Lift:
    # The result of lifting can be the identity.
    # The target of the handle can be an equalizer, but if the handle
    # is a lift, then some flattening must be applied.
    # When the target of the handle is an equalizer and the handle is not
    # a lift, the new target is still a flat equalizer.

    eqs = f.value
    handle = eqs.handle
    if isinstance(handle, Lift):
        hsup = handle.sup
        assert not isinstance(hsup, Lift)
        # The target of sup can still be an equalizer, but in this case
        # the target of sup will not be the sup of of the target of handle,
        # but just the an equalizer with the same sup and subset of its requirements,
        # i.e. a superobject.
    else:
        hsup = handle

    obj = handle.target
    requirements = eqs
    # The resulting equalizer will include all the requirements of `handle.target`.
    eqr, oreqs = _equalizer(obj, requirements)
    # If handle was a lift, it will get reconstructed.
    for req in oreqs:
        # We lift the handle `h` so that it can be composed with `req`.
        # The equality must match the fork compositions! Hence we normalize.
        # When ordering the reqs we guarantee that the requirements are available
        # for this lift to be valid. Using mor for gradual lifting requires
        # flattening the Lift so that the composition with req corresponds to
        # the equality. One must also flatten the equalizer targets.
        # The composition of the lift with an inclusion results in a longer lift.
        # One changes the req not the handle, otherwise the final lift won't be correct.
        #if isinstance(mor, Lift):
        #    pass
        #i_mor = compose(El((i, mor), f.eqs)) # Use inc not mor
        #j_mor = compose(El((j, mor), f.eqs))
        # The inclusion is precisely the one created during equalizer type-checking.
        # One must make sure that the target of the handle is the source of this inclusion.
        # The source of this inclusion is an associated (i.e. non flat) equalizer.
        # The problem with this equalizer is that is not the appearing in eqs[req].
        # Hence, we need to flatten it.
        # Even worse, the compositions in eqs[req] are based on the original handle
        # and not on the composition of a lift (handle) and an inclusion.
        # This seems to point to the need of having flattening at the model level,
        # or at least have composition simplification of lift with inclusion
        # (lift composed with inclusion becomes lift or the sup morphism).
        # The latter will probably work since both the lift and the inclusion
        # will have associated equalizers (as target and source respectively).
        #h = _flat_lift(hsup, plex.source(req[0]))
        _ = lex.lift(El((h, req, eqs[req]), f.eqs))



