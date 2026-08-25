from abc import ABCMeta, abstractmethod
from typing import Iterator, Collection, Iterable
from collections.abc import Sized

from .category import Obj, Mor, Composition, Parallel
from ..equality import Eq

def _split_parallel(par: Parallel):
    def head(p: Parallel):
        if isinstance(p.source, Equalizer):
            return p.source.ordered

        return ()

    def tail(p: Parallel):
        # Gives all requirements not appearing in the source.
        if isinstance(p.source, Equalizer):
            sreqs = p.source.requirements
        else:
            sreqs: Collection[tuple[Mor, Mor]] = frozenset()

        for q in p.pairs:
            yield q, q in sreqs

    return head(par), tuple(tail(par))

class BaseFork(Sized, metaclass=ABCMeta):
    __slots__ = ()

    @abstractmethod
    def handle(self) -> Mor:
        pass

    @abstractmethod
    def parallel(self) -> Parallel:
        pass

    def eq(self) -> Iterator[Eq[Mor]]:
        h = self.handle()
        for i, j in self.parallel():
            yield Eq[Mor](
                Composition.strict((i, h)),
                Composition.strict((j, h)),
            )

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.handle() == x.handle()
            and self.parallel() == x.parallel()
        )

class Fork(BaseFork):
    __slots__ = ('mor', 'pairs')
    mor: Mor
    pairs: tuple[tuple[Mor, Mor], ...]

    def handle(self):
        return self.mor

    def parallel(self):
        return Parallel(self.mor.target, self.pairs)

    def __len__(self):
        return len(self.pairs)

    def __init__(self, mor: Mor, pairs: Iterable[tuple[Mor, Mor]]):
        self.mor = mor
        self.pairs = tuple(pairs)

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.mor == x.mor
            and self.pairs == x.pairs
        )

ReqList = tuple['ReqList | tuple[()]', tuple[tuple[tuple[Mor, Mor], bool], ...]]

class Equalizer(Obj, BaseFork):
    __slots__ = ('sup', 'requirements', 'ordered', 'frozen')
    sup: Obj
    requirements: set[tuple[Mor, Mor]]
    ordered: ReqList
    frozen: bool

    def restrict(self, mor: Mor):
        # This assumes that the restrictions makes. No type-checking.
        h = Inclusion(self)
        res = Composition.strict((mor, Lift.strict(h, mor.source)))
        assert res == Composition.strict((mor.extend(), h))
        return res

    def flat_requirements(self):
        def _flat(reqs: ReqList) -> Iterator[tuple[Mor, Mor]]:
            head, tail = reqs
            if head:
                yield from _flat(head)

            for r, _ in tail:
                yield r

        return _flat(self.ordered)

    def __len__(self):
        # This has to be the length of the `parallel` argument.
        # This corresponds to the interpretation of the equalizer as as fork.
        return len(self.ordered[1])

    def is_subobject(self, obj: 'Obj'):
        if isinstance(obj, Equalizer):
            return self.requirements.issuperset(obj.requirements)

        return self.sup == obj

    def copy(self):
        res = super().__new__(type(self))
        res.sup = self.sup
        res.requirements = set(self.requirements)
        res.ordered = self.ordered
        res.frozen = True
        return res

    def relax(self):
        fulfilled, unfulfilled = self.ordered
        if len(self.requirements) == len(unfulfilled):
            return self.sup

        assert len(fulfilled) > 0
        res = self.copy()
        res.ordered = fulfilled

        # Can't remove unfulfilled requirements that appear in the source
        # of the parallel (redundant requirements).
        res.requirements.difference_update(
            p for p, red in unfulfilled
            if not red
        )
        return res

    def parallel(self):
        return Parallel(self.relax(), (p for p, _ in self.ordered[1]))

    def handle(self):
        # For all requirements in `self.ordered[1]` there is only one
        # handle.
        inc = Inclusion(self)
        return Lift.strict(inc, self.relax())

    def eq(self):
        # A more efficient `eq`.
        # This gives the same result as the method in super, so not all
        # equalities are yielded. This appears to have no use, since one
        # cannot use for registering equalizer equalities given the overly
        # restrictive source.
        for (i, j), _ in self.ordered[1]:
            yield Eq[Mor](
                self.restrict(i),
                self.restrict(j),
            )

    def verify(self, e: Eq[Mor]):
        s, t = e
        return (
            s.extend(),
            t.extend(),
        ) in self.requirements

    @classmethod
    def _reuse_source(cls, src: Obj) -> tuple[Obj, set[tuple[Mor, Mor]]]:
        if isinstance(src, Equalizer):
            sup = src.sup
            assert not isinstance(sup, Equalizer)
            requirements = src.requirements
            if src.frozen:
                return sup, set(requirements)

            del src.sup
            del src.ordered
            del src.requirements
            return sup, requirements

        return src, set()

    def __init__(self, parallel: Parallel, _allow_no_requirements: bool = False):
        super().__init__()
        src = parallel.source
        self.ordered = _split_parallel(parallel)
        if not (self.ordered[1] or _allow_no_requirements):
            raise ValueError("No requirements")

        self.sup, self.requirements = self._reuse_source(src)
        self.requirements.update(parallel.pairs)
        self.frozen = True
        # It is entirely possible for the `Parallel` instance
        # to include requirements that are tautological with respect to
        # the source! Such requirements can't be removed when recovering the
        # source. It is possible for the source to be the same as the equalizer,
        # in which case the handle ends up being the identity.

    # def __init__(
    #     self, sup: Obj,
    #     requirements: Iterable[tuple[Mor, Mor]],
    # ):
    #     super().__init__()
    #     it = iter(requirements)
    #     self.requirements = self._reuse_first(it)
    #     self.requirements.update(it)
    #     self.frozen = False
    #     self.sup = sup # TODO: Infer from requirements?

    def accepts(self, x: object):
        # This only affects public interface, the rest gets handled through
        # static type checking. Cf. trusted/proven modules.
        # The elements resulting from evaluation can't possibly be compared through
        # intensional equalities used for morphisms, since there is no way to introduce
        # such equalities for elements.s
        return self.sup.accepts(x) and all(
            s.ev(x) == t.ev(x)
            for s, t in self.requirements
        )

    def __eq__(self, x: object):
        # This does not coincide with fork equality.
        # Equality for type checking.
        return self is x or (
            isinstance(x, type(self))
            and self.sup == x.sup
            and self.requirements == x.requirements
        )

class Inclusion(Mor):
    __slots__ = ()

    def __init__(self, source: Equalizer):
        super().__init__(source, source.sup)
        # Just like in `Projection` we validate the label, here we check
        # that the inclusion is valid based on superobject?
        # A lift can be an identity. The identity is also an inclusion
        # (from the equalizer of identities). Some inclusions can be obtained
        # by lifting. It makes sense then, for sake of normalization, that
        # these inclusions be obtained as lifts (identity can remain as both
        # inclusion and lift). Allow lift through the identity?
        self.name = '<-'

    def ev(self, x: object):
        # Notice that x.value can itself be an instance of El.
        # As in other classes defining `ev`, this does not need to fail when
        # `x` is not accepted by the source.
        return x

    def reduce(self, mor: Mor):
        # This has no responsibility to do any type-checking.
        if isinstance(mor, Lift) and isinstance(self.source, Equalizer):
            return mor.sup

        return None

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.source == x.source
        )

    def extend(self):
        return Composition(self.target)

class BaseLift(Sized, metaclass=ABCMeta):
    __slots__ = ()

    @property
    @abstractmethod
    def mor(self) -> Mor:
        pass

    def parallel(self):
        target = self.mor.target
        return target.parallel()

    @classmethod
    def ensure(cls, mor: Mor):
        if isinstance(mor, cls):
            return mor

        return AbstractLift(mor)

    def __eq__(self, x: object):
        # `parallel()` is not guarantied to be the same.
        return self is x or (
            isinstance(x, type(self))
            and self.mor == x.mor
            and self.parallel() == x.parallel()
        )

    def __len__(self):
        target = self.mor.target
        if isinstance(target, Equalizer):
            return len(target)

        return 0

class AbstractLift(BaseLift):
    __slots__ = ('_mor',)
    _mor: Mor

    @property
    def mor(self):
        return self._mor

    def __init__(self, mor: Mor):
        self._mor = mor

class Lift(Mor, BaseLift):
    __slots__ = ('sup',)
    sup: Mor

    def extend(self):
        # We could actually extend lifts when their supermorphism can be extended
        # while keeping the lift valid, but checking this would be too complicated.

        if isinstance(self.sup, Inclusion):
            return Composition(self.target)

        return self

    @property
    def mor(self):
        return self

    def __init__(self, mor: Mor, target: Equalizer):
        # When building from `mor` and `target`, we skip the (extensionally strict)
        # subobject check here, since doing it would incur quadratic time during
        # variadic-from-binary construction. Morover, we should actually be building
        # from a fork (just as pairing is built from a span), and the fork check should
        # be carried out in `proven`.
        # For simplicity, we follow the approach of providing the target.
        # The subobject check is the fork check in `proven`.
        # Requiring strictness here is not possible because of the afore-mentioned
        # quadratic time issue.
        super().__init__(mor.source, target)
        self.name = mor.name

        if isinstance(mor, Lift):
            self.sup = mor.sup
        else:
            self.sup = mor

    @classmethod
    def strict(cls, mor: Mor, target: Obj):
        # The == comparisons here usually return False, so they don't impact performance too much.
        if mor.target == target:
            return mor

        if not isinstance(target, Equalizer):
            raise ValueError('Requires equalizer target')

        res = cls(mor, target)

        # Max lift of inclusion is identity
        if isinstance(res.sup, Inclusion) and res.sup.source == target:
            return Composition(target)

        return res

    def ev(self, x: object):
        return self.sup.ev(x)

    def reduce(self, mor: Mor):
        sup_r = self.sup.reduce(mor)
        if sup_r is not None:
            target = self.target
            assert isinstance(target, Equalizer)
            # TODO: Should we use strict?? Perhaps not.
            return Lift(sup_r, target)

        return None

    def __eq__(self, x: object):
        # Equality as morphism
        return self is x or (
            isinstance(x, type(self))
            and self.target == x.target
            and self.sup == x.sup
        )
