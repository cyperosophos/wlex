from abc import ABCMeta, abstractmethod
import weakref

from .category import Obj, Mor, Composition, ProjError
from .cart import WRef
from ..equality import Eq
from ..proven import ValidationError

# TODO: Normalize equalities (and requirements) by factoring out
# epis and monos? Probably overkill.

class Parallel:
    __slots__ = (
        'source',
        '_i', '_j',
        'idx',
        'equalizer',
    )
    source: Obj
    _i: Mor
    _j: Mor
    idx: tuple[int, ...]
    equalizer: WRef['Equalizer']

    def __init__(self, source: Obj, i: Mor, j: Mor, idx: tuple[int, ...]):
        # Lifting an inclusion based on builtin subset operation
        # has the only disadvantage that it cannot rely on intensional equalities.
        # The `Parallel` class avoids having to compose with an inclusion, whose
        # target might end up being discarded, and which has to be removed when
        # normalizing the requirement.
        # Extending here is correct since the common source is already determined.
        self._i = i
        self._j = j
        self.source = source
        self.idx = idx
        self.equalizer = lambda: None

        # Repeated requirements must not be allowed, because then the dict
        # of requirements in the Equalizer would be inconsistent.
        # Of course the equalizer still exist (meaning that the lifts can be constructed)
        # just not the parallel to produce it.
        # TODO: Should this actually be in context?
        if isinstance(source, Equalizer):
            if (i.extend(), j.extend()) in source.requirements:
                raise ValueError('Repeated requirement')

    def _restrict(self, mor: Mor):
        p = self.source.proj(self.idx)
        return Composition.strict(p.target.restrict(mor), p)

    def is_valid(self):
        source = self.source.component(self.idx)
        if not (
            source.is_subobject(self._i.source)
            and source.is_subobject(self._j.source)
        ):
            raise ValidationError('`source` must be subobject.')

        # Recall that there is no such thing as a public eq which need to be checked
        # by the public interface.
        if self._i.target != self._j.target:
            raise ValidationError('Must have equal targets')

    def i(self):
        return self._restrict(self._i)

    def j(self):
        return self._restrict(self._j)

    def projected(self, source: Obj, idx: int):
        # TODO: !!! idx should actually be tuple[int, ...].
        # This could be a deep component.
        # TODO: Should there be a mapping of components to indices?
        #       (to be used in proj product -> object with no idx)
        # TODO: proj should be deep!

        # When an index is given, we take the existence of this parallel as having being inferred
        # from the existence of the parallel without the index.
        # TODO: Why don't just access the original parallel??
        # TODO: source = self.source.component(self.idx)
        # return Parallel(
        #     source,
        #     self._i,
        #     self._j,
        #     -1,
        # )
        # TODO: Since it is context where we get rid of params with equalizers,
        # it should also be there where we give the existence of parallels whose
        # existence was originally a consequence of the existence of the remove params.
        # raise TypeError("...")
        # TODO: Actually instead of subclassing param and parallel it is better to just
        # provide functions with checks in context that create that needed diagrams.

        if isinstance(self.source, Equalizer):
            source = Equalizer(self.source.par.projected(source, idx))

        # This is valid when `self.source` (not an equalizer) is the component at
        # `idx` of (equalizer of) product `source` (no equalizer components).
        if self.source != source.component(idx):
            raise ValueError("Wrong source")

        return Parallel(
            source,
            self._i,
            self._j,
            idx,
        )

    # def projected(self, proj: Projection):
        # The parallel precomposed with restrict-lifted projection.
        # TODO: Match source and target each time composition is instantiated directly (or using `strict`).
        # The target of the projection is expected to not be an equalizer.
        # One takes self.source, which may be an equalizer, ...
        # The only product involved is the one with no equalizer among its components.
        # We need to determine what data we'll normally have available to make this construction.
        # if self.source != proj.target:
        #     raise ValueError("Invalid proj")

class BaseFork(metaclass=ABCMeta):
    __slots__ = ()
    par: Parallel

    @abstractmethod
    def mor(self) -> Mor:
        pass

    def eq(self) -> Eq[Mor]:
        h = self.mor()
        return Eq[Mor](
            Composition.strict(self.par.i(), h),
            Composition.strict(self.par.j(), h),
        )

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.mor() == x.mor()
            and self.par == x.par
        )

class Fork(BaseFork):
    __slots__ = ('_mor', 'par')
    _mor: Mor

    def mor(self):
        return self._mor

    def __init__(self, mor: Mor, par: Parallel):
        self._mor = mor
        self.par = par

class Equalizer(Obj, BaseFork):
    __slots__ = ('sup', 'requirements', 'length', 'par')
    sup: Obj
    # TODO: !!! idx should be part of the key because we may have the
    # same pair for different components? Or should we map to multiple idx?
    requirements: dict[tuple[Mor, Mor], tuple[int, int]] # This keeps the order. Requires Python >= 3.7.
    # Second int is the idx of the component.
    length: int

    def component(self, idx: tuple[int, ...]) -> Obj:
        sup = self.sup.component(idx)
        # There may be no requirements.


    def proj(self, target: Obj | tuple[int, ...], _depth: int = 1):
        # This works only with expanded products
        try:
            return super().proj(target)
        except ProjError:
            pass

        # TODO: It seems more consistent to keep track of how requirements map to
        # components of the superobject (when it is a product), so that the result
        # of projection is the expected one (equalizer components).
        # When idx is given we get the component corresponding to idx.
        # When a target object is given we do nothing unless the object is an equalizer
        # in which case we only need to check that the requirements of the target
        # appear in self. With equalizer we first use its superobject as the target.
        # The result of proj can be a composition of projections (not just a pairing or projection).
        # We would need a special attribute in both Composition and Pairing
        # to keep track of the actual idx tree that results from proj and then
        # use this idx tree to find the requirements.
        h = self.sup.proj(target)
        return Lift((
            Composition.strict(res, Inclusion(self)),
            self.component(),
        ))

        # For consistency we want this to return a morphism whose target is
        # `target`. The way we deal with equalizers of products is by extracting
        # their superobject and passing it as the `target` here. The goal of
        # `proj` is to make superobjects coincide so that restrict-lifting can
        # be applied, and then `incl`.
        return None

    # @classmethod
    # def expand(cls, obj: Obj):
        # The morphism from the product is a lift of the pairing
        # of the inclusions.
        # The morphism from the equalizer is a pairing of all projections
        # (precomposed with the inclusion and then lifted).
        # It seems reasonable that the tautological quality of requirements
        # is the the same in the product expanded or not.
        # Hence, we precompose requirements with restricted-lifted projections.
        # Expand is deep (recursive).
        # Steps:
        # - Get the superobject.
        # - Collect all requirements.
        # - Precompose with restricted lifted projections.
        # - Build equalizer.
        # One needs existence of Parallel. The reasoning here is that one has
        # the existence of certain equalizers given their construction as products.
        # Based on this (assumed) theorem, there is a method of Parallel
        # which allows the instation of isomorphic concrete equalizer, but of course
        # the inability to construct the concrete equalizer does not refute the
        # existence of the equalizer.
        # Since the elements of equalizers look exactly like the elements of their
        # superobjects, a simpler (and opposite) approach is to disallow product
        # params where one of the objects is an equalizer.
        # pass

    def incl_opt(self, target: Obj | None):
        res = super().incl_opt(target)
        if res:
            return res

        h = Inclusion(self)
        if target is None or self.sup == target:
            return h

        assert isinstance(target, Equalizer)
        if self.is_subobject(target):
            return Lift((h, target))

        return None

    def _incl(self, target: Obj) -> Mor:
        # TODO: Check that this gives the same result as `incl`.
        if not isinstance(target, Equalizer):
            return Inclusion(self)

        return Lift(Fork(
            self._incl(target.par.source),
            target.par,
        ))

    def mor(self):
        return Lift(Fork(
            self._incl(self.par.source),
            self.par),
        )

    def restrict(self, mor: Mor):
        # This assumes that the restriction makes sense. No type-checking.
        # If `mor.source` gets reused and `mor` is precomposed with an inclusion,
        # this will still work since the inclusion gets reduced with the lift.

        # Actually, this composition is always correct.
        return Composition.strict(mor, self.incl(mor.source))
        # We need to be able to restrict even if mor can't be extended.
        #return Composition.strict(mor.extend(), Inclusion(self))

    def is_subobject(self, obj: 'Obj'):
        if isinstance(obj, Equalizer):
            reqs = self.requirements
            length = self.length
            return (
                self.sup == obj.sup
                and all(
                    reqs.get(req, length) < length
                    for req, _ in zip(obj.requirements, range(obj.length))
                )
            )

        return self.sup == obj

    def eq(self):
        # A more efficient `eq`.
        # This gives the same result as the method in super, so not all
        # equalities are yielded. This appears to have no use, since one
        # cannot use for registering equalizer equalities given the overly
        # restrictive source.
        return Eq[Mor](
            self.restrict(self.par.i()),
            self.restrict(self.par.j()),
        )

    def verify(self, e: Eq[Mor]):
        s, t = e
        # What if the equality only applies for a subset of the intersection of the sources?
        # This would only concern us if we were searching the equality among the proofs.
        # The source of the equality is the equalizer, so the equality is fulfilled.

        # TODO: Equality has to be valid. Perhaps guaranty this during instantiation.
        # We need to make sure that the source is a subobject of self.
        # return s.source.is_subobject(self) and (
        #     s.extend(),
        #     t.extend(),
        # ) in self.requirements

        # Get the idx


    @classmethod
    def _first_requirements(cls, src: Obj) -> tuple[Obj, dict[tuple[Mor, Mor], int]]:
        if isinstance(src, Equalizer):
            sup = src.sup
            assert not isinstance(src, Equalizer)
            requirements = sup.requirements
            if sup.length == len(requirements):
                return sup, requirements

            return sup, requirements.copy()

        return src, {}

    def __new__(cls, par: Parallel):
        res = par.equalizer()
        if res is None:
            return super().__new__(cls)

        return res

    def __init__(self, par: Parallel):
        if par.equalizer() is not None:
            return

        par.equalizer = weakref.ref(self)
        super().__init__()
        self.sup, requirements = self._first_requirements(par.source)
        requirements[(par.ext_i, par.ext_j)] = len(requirements)
        self.length = len(requirements)
        self.requirements = requirements
        # It is entirely possible for the `Parallel` instance
        # to include requirements that are tautological with respect to
        # the source.

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
        if isinstance(mor, Lift):
            return mor.sup

        return None

    def __eq__(self, x: object):
        return self is x or (
            isinstance(x, type(self))
            and self.source == x.source
        )

    def extend(self):
        return Composition(self.target)

    # def lift(self, target: Obj) -> Mor:
    #     if self.target == target:
    #         return self

    #     assert isinstance(target, Equalizer)
    #     if self.source == target:
    #         return Composition(target)

    #     if not self.source.is_subobject(target):
    #         raise ValueError("Can't lift")

    #     return Lift((self, target))

class Lift(Mor):
    __slots__ = ('sup',)
    sup: Mor

    def extend(self):
        # We could actually extend lifts when their supermorphism can be extended
        # while keeping the lift valid, but checking this would be too complicated.

        if isinstance(self.sup, Inclusion):
            return Composition(self.target)

        return self

    def __init__(self, fork: BaseFork | tuple[Mor, Equalizer]):
        # When building from `mor` and `target`, we skip the (extensionally strict)
        # subobject check here, since doing it would incur quadratic time during
        # variadic-from-binary construction. Morover, we should actually be building
        # from a fork (just as pairing is built from a span), and the fork check should
        # be carried out in `proven`.
        # For simplicity, we follow the approach of providing the target.
        # The subobject check is the fork check in `proven`.
        # Requiring strictness here is not possible because of the afore-mentioned
        # quadratic time issue.
        if isinstance(fork, tuple):
            mor, target = fork
        else:
            mor = fork.mor()
            target = Equalizer(fork.par)

        super().__init__(mor.source, target)
        self.name = mor.name

        # Equalizer is flat, so Lift must also be flat.
        if isinstance(mor, Lift):
            self.sup = mor.sup
        else:
            self.sup = mor

    @classmethod
    def strict(cls, fork: BaseFork):
        res = cls(fork)
        # Max lift of inclusion is identity
        if isinstance(res.sup, Inclusion) and res.source == res.target:
            return Composition(res.target)

        return res

    def ev(self, x: object):
        return self.sup.ev(x)

    def reduce(self, mor: Mor):
        t = self.target
        assert isinstance(t, Equalizer)

        m = t.mor().reduce(mor)
        if m is None:
            return None

        # m could be an inclusion. e.g. sup is a projection and mor
        # is a pairing with an inclusion component.
        return Lift.strict(Fork(m, t.par))

    def __eq__(self, x: object):
        # Equality as morphism
        return self is x or (
            isinstance(x, type(self))
            and self.target == x.target
            and self.sup == x.sup
        )
