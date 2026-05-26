"""Base classes for cells and cell exceptions"""
from collections.abc import Callable, Sequence, Collection, Iterator, Iterable
from collections import defaultdict
from abc import ABCMeta, abstractmethod
from typing import Optional
from enum import Enum

class Error(Exception):
    """Base class for cell exceptions"""

class Unfit(Error):
    """Cell is unfit for conversion."""

    def __init__(self, message: str, frm: 'Cell', to: 'Cell'):
        super().__init__(message)
        self.frm = frm
        self.to = to

    def __str__(self):
        frm = self.frm
        to = self.to
        return f"{super().__str__()} {frm=} {to=}"

class ObjUnfit(Unfit):
    """Object is unfit for conversion."""

class TargetUnfit(ObjUnfit):
    """Target is unfit for conversion."""

class SourceUnfit(ObjUnfit):
    """Source is unfit for conversion."""

class MorUnfit(Unfit):
    """Morphism is unfit for conversion."""

class STargetUnfit(ObjUnfit):
    """Setoid target is unfit for conversion."""

class SSourceUnfit(ObjUnfit):
    """Setoid source is unfit for conversion."""

class TargetInvalid(Error):
    """Invalid value for target during morphism evaluation

    This error is only raised during defensive evaluation.
    """
    def __init__(self, message: str, x: 'Defensive', res: object = None):
        super().__init__(message)
        self.x = x.copy()
        self.res = res

    def __str__(self):
        x = self.x
        res = self.res
        return f"{super().__str__()} {x=} {res=}"

class TargetFailure(TargetInvalid):
    """Invalid due to unfulfilled equalities

    The source of these equalities is the target of the morphism. Being due to
    an exception unable to establish that all equalities are fulfilled also
    counts as this exception.
    """
    def __init__(
            self, message: str, x: 'Defensive', res: object = None,
            failed: Sequence['Eq'] = (),
        ):
        super().__init__(message, x, res)
        self.failed = failed

    def __str__(self):
        failed = self.failed
        return f"{super().__str__()} {failed=}"

class TargetMismatch(TargetInvalid):
    """Invalid due to not being accepted by the target

    If there was no value to check against target then `res` is not provided.
    This occurs after an exception, which will then be the `__cause__` of this
    exception. Being unable due to an exception to check that the value gets
    accepted also counts as this exception.
    """

class SourceInvalid(Error):
    """Invalid value for source during morphism evaluation

    This error is only raised during public evaluation. The public function that
    evaluates the morphism will raise a TypeError from this exception.
    """
    def __init__(self, message: str, x: object):
        super().__init__(message)
        self.x = x

    def __str__(self):
        x = self.x
        return f"{super().__str__()} {x=}"

class SourceFailure(SourceInvalid):
    """Invalid due to unfulfilled equalities

    The source of these equalities is the source of the morphism. Being unable
    due to an exception to establish that all equalities are fulfilled also
    counts as this exception.
    """
    def __init__(self, message: str, x: object, failed: Sequence['Eq'] = ()):
        super().__init__(message, x)
        self.failed = failed

    def __str__(self):
        failed = self.failed
        return f"{super().__str__()} {failed=}"

class SourceMismatch(SourceInvalid):
    """Invalid due to not being accepted by the source

    Being unable due to an exception to check that the value gets accepted also
    counts as this exception.
    """

class VerificationError(Error):
    """Unable to verify equality"""
    def __init__(self, message: str, eq: 'Eq'):
        super().__init__(message)
        self.eq = eq

    def __str__(self):
        eq = self.eq
        return f"{super().__str__()} {eq=}"

class VerificationSsourceError(VerificationError):
    """Unable to evaluate setoid source due to exception"""

class VerificationStargetError(VerificationError):
    """Unable to evaluate setoid source due to exception"""

class VerificationSamenessError(VerificationError):
    """Unable to establish sameness due to exception"""
    def __init__(self, message: str, eq: 'Eq', s: object, t: object):
        super().__init__(message, eq)
        self.s = s
        self.t = t

    def __str__(self):
        s = self.s
        t = self.t
        return f"{super().__str__()} {s=} {t=}"

class Defensive:
    """Wraps argument passed to defensive morphisms"""
    __slots__ = 'value', 'stack'
    value: object
    stack: list['Mor']

    def __init__(self, value: object):
        self.value = value
        self.stack = []

    def copy(self):
        """Create a copy of `self`"""
        # No need to this when evaluating pairings, because the evaluation of
        # the components occurs sequentially.
        res = Defensive(self.value)
        res.stack = [*self.stack]
        return res

    def exit(self, value: object):
        """Called when evaluation returns"""
        self.stack.pop()
        res = type(self)(value)
        res.stack = self.stack
        return res

    @classmethod
    def enter(cls, x: object, mor: 'Mor'):
        """Called when evaluation starts"""
        if not isinstance(x, cls):
            x = cls(x)
        x.stack.append(mor)
        return x

class Name:
    __slots__ = 'parent', 'base'
    parent: Optional['Name']
    base: str

    def __init__(self):
        self.parent = None
        self.base = ''

    def __iter__(self) -> Iterator[str]:
        yield self.base
        if self.parent:
            yield from iter(self.parent)

    def __str__(self):
        return '.'.join(reversed(list(self)))

class Obj(metaclass=ABCMeta):
    """Base class for objects (0-cells)"""
    __slots__ = ('name',)
    name: Name
    eqs: dict['Obj', list[tuple['Eq', bool]]] = defaultdict(list)

    def __init__(self):
        self.name = Name()

    def trim(self, obj: 'Obj') -> Optional['Mor']:
        """Gives morphism that converts `self` into `obj`"""
        # Inclusion conversions always make sense.
        if self.identical(obj):
            return self.identity()

        return None

    @abstractmethod
    def accepts(self, x: object) -> bool:
        """`self` accepts `x` as element."""
        # `accepts` may require verication of equalities in subclass,
        # specifically in equalizers. In this case `self` is the source
        # of the equalities.

    @abstractmethod
    def same(self, x: object, y: object) -> bool:
        """`x` and `y` are the same as elements of object `self`.

        This assumes that `self` accepts `x` and `y`. If two elements are the
        same, then they are equal, but the converse dos not hold in general.
        The preimage of `True` under `self.same` is a reflexive and symmetric
        relation.
        """

    def failed_eqs(self, x: object):
        """Equalities unfulfilled by `x`

        Notice that this may raise a `TargetInvalid` error due to defensive type
        checking.
        """
        # This is different from `accepts`, `same`, etc., because it returns the
        # reasons for failing rather than just indicating that failure occurred.
        # Perhaps the fact the these equalities are not tied to the object and
        # may therefore be more cumbersome to track justifies said difference.
        return [
            eq for eq, _ in self.eqs[self]
            if not eq.verify(x)
        ]

    def failed_public_eqs(self, x: object):
        """Public equalities unfulfilled by `x`

        "Public" means that the equality is not guaranteed to be fulfilled by
        aguments of the public interface.
        """
        return [
            eq for eq, public in self.eqs[self]
            if public and eq.verify(x)
        ]

    def require_eq(self, eq: 'Eq', public: bool):
        """Associate equality `eq` to `self`"""
        self.eqs[self].append((eq, public))

    def __str__(self):
        if hasattr(self, 'name'):
            return '.'.join(self.name)
        return NotImplemented

    def __repr__(self):
        return f'Obj("{self!s}")'

    def __eq__(self, x: object):
        return isinstance(x, Obj) and self.identical(x)

    def __hash__(self):
        return hash(self.hint())

    def hint(self) -> object:
        """If two objects are identical, then their hints are ==.

        The converse does not hold in general. This is useful for
        computing `hash`.
        """
        return id(self)

    def identical(self, x: 'Obj') -> bool:
        """`x` is admitted instead of `self` as source or target.

        This is possible because `self.accepts` (resp. `self.same`) is in this
        case the same function as `x.accepts` (resp. `x.same`). The converse
        does not hold in general. The preimage of `True` under `Obj.identical`
        is a reflexive and symmetric relation. The identity morphism acts as an
        isomorphism from `self` to `x`.
        """
        return (
            self is x
            or (bool(getattr(x, 'identity_priority', False)) and x.identical(self))
        )


    @property
    def sup(self):
        """Superobject, i.e. largest object containing `self`"""
        return self

    @property
    def requirements(self) -> frozenset[tuple['Mor', 'Mor']]:
        return frozenset()

    def identity(self) -> 'Mor':
        """Models morphism `category.identity`"""
        raise TypeError("Requires CategoryObj")

    def incl(self, obj: Optional['Obj'] = None) -> 'Mor':
        """Inclusion morphism"""
        # Analogous to `proj`
        if obj is None or self.identical(obj):
            return self.identity()

        raise ValueError("Not included")

    def lift(self, mor: 'Mor') -> 'Mor':
        if self.identical(mor.target):
            return mor

        raise ValueError("Can't lift")

    # def extend(self, mor: 'Mor') -> 'Mor':
    #     if self.identical(mor.target):
    #         return mor

    #     raise ValueError("Can't extend")

    # TODO: Why not Sequence['Mor']?
    @classmethod
    def vcomposition(cls, *factors: 'Mor') -> 'Mor':
        """Variadic composition"""
        raise TypeError("Requires CategoryObj")

    @classmethod
    def terminal(cls) -> 'Obj':
        """Models morphism `cart.terminal`"""
        raise TypeError("Requires CartObj")

    def terminal_mor(self) -> 'Mor':
        """Models morphism `cart.terminal_mor`"""
        raise TypeError("Requires CartObj")

    def product(self, y: 'Obj') -> 'Obj':
        """Models morphism that gets source of span `cart.product`"""
        raise TypeError("Requires CartObj")

    @classmethod
    def vproduct(
        cls,
        params: Sequence[tuple[str | int, 'Obj']],
        no_repeat: bool = False,
    ) -> 'Obj':
        """Variadic product"""
        raise TypeError("Requires CartObj")

    def vproduct_mor(
        self,
        params: Sequence[tuple[str | int, 'Mor']],
    ) -> 'Mor':
        """Variadic product morphism"""
        raise TypeError("Requires CartObj")

    def proj(self, label: str | int) -> 'Mor':
        """Projection, that is leg of product span"""
        # if label == '':
        #     return self.identity()

        return self.terminal_mor()

    def iso_relabeling(
        self, relabeling: Iterable[tuple[str | int, str | int]],
    ) -> Iterator[tuple[str | int, str | int]]:
        raise TypeError("Requires Product")

    def sequence_relabeling(
        self, relabeling: Sequence[str | int],
    ) -> Iterator[tuple[str | int, str | int]]:
        raise TypeError("Requires Product")

    def with_labels(
        self, relabeling: Iterable[tuple[str | int, str | int]],
    ) -> 'Obj':
        raise TypeError("Requires Product")

    def relabel(
        self, relabeling: Iterable[tuple[str | int, str | int]],
    ) -> 'Mor':
        raise TypeError("Requires Product")

    @staticmethod
    def inverse_relabeling(relabeling: Iterable[tuple[str | int, str | int]]):
        # The goal is that the target of
        # `self.with_labels(relabeling).relabel(self.inverse_relabeling(relabeling))`
        # is just `self` in the case of an iso relabeling. Otherwise, it is just
        # a "multicomponent".

        for k, v in relabeling:
            yield v, k

    @staticmethod
    def sublabeling(relabeling: Iterable[str | int]):
        for k in relabeling:
            yield k, k

    def fork(self, ssource: 'Mor', starget: 'Mor') -> 'Eq':
        """Requirement of subobject"""
        raise TypeError("Requires Subobject")

    def subobject(self, requirements: Collection[tuple['Mor', 'Mor']],) -> 'Obj':
        raise TypeError("Requires LexObj")

    def join(self, obj: 'Obj') -> tuple['Mor', 'Mor']:
        raise TypeError("Requires CartObj")

class Mor(metaclass=ABCMeta):
    """Base class for morphisms (1-cells)"""
    __slots__ = 'name', 'source', 'target'#, '_hat'
    name: Name
    source: Obj
    target: Obj
    #_hat: tuple['Mor', 'Mor']
    depth = 0 # Used in LazyComposition

    # @property
    # def hat(self):
    #     """Hat equality associated to morphism"""
    #     # This raises AttributeError in the case of morphisms lacking a hat
    #     # equality.
    #     hat_source, hat_target = self._hat
    #     return Eq(hat_source, hat_target.compose(self))

    def expanded(self):
        """Underlying composition in the case of LazyComposition"""
        return self

    @abstractmethod
    def ev(self, x: object) -> object:
        """Element, to which morphism `self` maps `x`"""

    def public_ev(self, x: object):
        """Checks `x` against source before evaluation"""
        source = self.source

        if source.accepts(x):
            failed = source.failed_public_eqs(x)

            if failed:
                raise SourceFailure("Unfulfilled equalities:", x, failed)

            return self.ev(x)

        raise SourceMismatch("Not accepted by source:", x)

    def __init__(self, source: Obj, target: Obj):
        self.source = source
        self.target = target

    def __eq__(self, x: object) -> bool:
        return isinstance(x, Mor) and self.same(x)

    def __hash__(self):
        return hash(self.hint())

    def hint(self) -> object:
        """If two morphisms are identical, then their hints are ==.

        The converse does not hold in general. This is useful for
        computing `hash`.
        """
        return id(self)

    def same(self, x: 'Mor') -> bool:
        """`x` is admitted instead of `self` as ssource or starget`.

        This is possible because `self.ev` is in this case the same function as
        `x.ev`. The converse does not hold in general, and `self.target.same`
        may sometimes not return `True` when called on the result of `self.ev`
        and `x.ev`. The preimage of `True` under `Mor.same` is a reflexive and
        symmetric relation. If two morphisms are the same, then they have the
        same source (resp. target), and their equality is given by reflexivity.
        """
        # There are a few cases where one should (partially) verify the
        # signature, e.g. identity, to ensure that being the same implies having
        # the same signature. This returns False when the signatures don't
        # coincide even if the sameness comparison is actually nonsensical in
        # such case.
        return (
            x is self
            or (bool(getattr(x, 'sameness_priority', False)) and x.same(self))
        )

    def __str__(self):
        if hasattr(self, 'name'):
            return '.'.join(self.name)
        return NotImplemented

    def __repr__(self):
        return f'Mor("{self!s}: {self.source} -> {self.target}")'

    # def split(self) -> tuple['Mor', 'Mor']:
    #     """Separate comoposition into the first factors and last factor"""
    #     raise TypeError("Requires Composition")

    def ref(self) -> 'Eq':
        """Models morphism `category.ref`"""
        raise TypeError("Requires CategoryMor")

    def compose(self, g: 'Mor') -> 'Mor':
        """Models morphism `category.compose`"""
        raise TypeError("Requires CategoryMor")

    def pairing(self, q: 'Mor') -> 'Mor':
        """Models morphism `cart.pairing`"""
        raise TypeError("Requires CartMor")

    def pairing_unique(self, p: 'Mor', q: 'Mor') -> 'Eq':
        """Models morphism `cart.pairing_unique`"""
        raise TypeError("Requires CartMor")

    def exfit(self, source: Obj):
        if self.source.identical(source):
            return self

        return source.terminal_mor()

class PrimEv:
    __slots__ = ('func',)
    func: Callable[[object], object]

    def __init__(self, func: Callable[[object], object]):
        self.func = func

    def to_mor(self, source: Obj, target: Obj):
        return PrimMor(source, target, self.func)

    def __hash__(self):
        return hash(self.func)

class PrimMor(Mor):
    """Base of primitive morphisms

    Primitive morphisms are the ones for which the `ev` method must be defined
    after initialization, that is during execution of the theory, to which the
    primitive morphisms belong.
    """
    __slots__ = ('raw_ev')

    raw_ev: Callable[[object], object]

    def __init__(self, source: Obj, target: Obj, raw_ev: Callable[[object], object]):
        super().__init__(source, target)
        self.raw_ev = raw_ev

    def ev(self, x: object) -> object:
        # TargetInvalid can only get caught outside the call stack, so there is
        # never a need to pop from the stack list when raising such exception.
        # Defensiveness is set on the argument, not on specific morphisms. An
        # untrusted part makes the whole system untrusted.

        # When argument is defensive, the value returned by `ev` is checked
        # against the target of `self` and the equalities that have this target
        # as source. This dynamic type-checking is analogous to the one done
        # with respect to the source of `self`, which is only always required by
        # the public interface (and also includes checking equalities).
        if not isinstance(x, Defensive):
            return self.raw_ev(x)

        target = self.target

        try:
            res = self.raw_ev(x.value)
        except Exception as exc:
            raise TargetMismatch(
                "No result against which to accept target:", x,
            ) from exc

        try:
            accepts = target.accepts(res)
        except Exception as exc:
            raise TargetMismatch(
                "Unable to check if result is accepted:", x, res,
            ) from exc

        if accepts:
            try:
                failed = target.failed_eqs(res)
            except Exception as exc:
                raise TargetFailure(
                    "Unable to check if there are unfulfilled equalities", x,
                    res,
                ) from exc

            if failed:
                raise TargetFailure(
                    "Unfulfilled equalities:", x, res, failed,
                )

            return x.exit(res)
        raise TargetMismatch("Not accepted by target:", x, res)

MorStub = Mor | PrimEv

class Eq:
    """Base class for equalities (2-cells)"""
    # There is no distinction between proven and unproven equalities. All that
    # matters is that the equality be constructed through the operations provided
    # by the theory. Something similar would happen with morphisms if no `ev`
    # was needed. In this case we would forget the construction and just retain
    # the signature. `Mor` would have no need to be abstract. An unproven
    # equality is useful when it gets interpreted as `lex.Parallel`. In the
    # theory all equalities are proven, since all equalities have to be
    # constructed not just instantiated. An unproven equality gets composed with
    # a morphism and produces a proven equality, this is the case of equializer
    # requirements. Instances of this class are then better interpreted as
    # equality signatures, even loose ones, since globular conditions are not
    # yet checked at this stage. Recall that setoids are categories enriched
    # over TV.
    __slots__ = 'ssource', 'starget', 'proven'
    ssource: Mor
    starget: Mor
    proven: bool

    def __init__(self, ssource: Mor, starget: Mor):
        self.ssource = ssource
        self.starget = starget
        self.proven = False

    def verify(self, x: object):
        """Verify that `x` satisfies equality `self`"""
        ssource = self.ssource
        starget = self.starget

        try:
            s = ssource.ev(x)
        except TargetInvalid as err:
            raise VerificationSsourceError(
                "Unable to evaluate setoid source of equality:", self,
            ) from err

        try:
            t = starget.ev(x)
        except TargetInvalid as err:
            raise VerificationStargetError(
                "Unable to evaluate setoid target of equality:", self,
            ) from err

        try:
            return ssource.target.same(s, t)
        except Exception as exc:
            raise VerificationSamenessError(
                "Unable to verify sameness", self, s, t,
            ) from exc

    def __eq__(self, proof: object):
        return isinstance(proof, Eq) and self.parallel(proof)

    def __hash__(self):
        return hash(self.hint())

    def hint(self):
        """The signature of the equality

        Equalities are fully characterized by their setoid source and target,
        that is their signature."""
        return (self.ssource, self.starget)

    ssignature = hint

    def parallel(self, proof: 'Eq'):
        """Equalities that coincide in their signature are parallel."""
        if proof is self:
            return True
        return (
            self.ssource == proof.ssource
            and self.starget == proof.starget
        )

    # def __str__(self):
    #     # if hasattr(self, 'name'):
    #     #     return '.'.join(self.name)
    #     return NotImplemented

    def __repr__(self):
        return f'Eq("{self!s}: {self.ssource} == {self.starget}")'

    def sym(self) -> 'Eq':
        """Models morphism `category.sym`"""
        raise TypeError("Requires CategoryEq")

    def trans(self, g: 'Eq') -> 'Eq':
        """Models morphism `category.trans`"""
        raise TypeError("Requires CategoryEq")

    def compose_eq(self, e: 'Eq') -> 'Eq':
        """Models morphism `category.compose_eq`"""
        raise TypeError("Requires CategoryEq")

    def equalizer(self) -> Mor:
        """Models morphism `lex.equalizer`"""
        raise TypeError("Requires LexEq")

    def equalizer_pairing(self, mor: Mor) -> Mor:
        """Models morphism `lex.equalizer_pairing`"""
        raise TypeError("Requires LexEq")

    def equalizer_pairing_unique(self, mor: Mor, fmor: Mor) -> 'Eq':
        """Models morphism `lex.equalizer_pairing_unique`"""
        raise TypeError("Requires LexEq")

class Axiom(Enum):
    PRIVATE = False
    PUBLIC = True

class PrimEq(Eq):
    """Base of primitive equalities"""
    __slots__ = ()

    def __init__(self, ssource: Mor, starget: Mor, public: bool | Axiom):
        # Trusting the target of a primitive morphism is analogous to not
        # providing a proof when assuming a primitive equality (especially a non
        # public one).
        super().__init__(ssource, starget)
        if isinstance(public, Axiom):
            public = public.value

        self.ssource.source.require_eq(self, public)
        self.proven = True

Cell = Obj | Mor | Eq
EqStub = Eq | Axiom
