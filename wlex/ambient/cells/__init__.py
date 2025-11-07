"""Base classes for cells and cell exceptions"""
from functools import wraps
from collections.abc import Callable, Sequence
from collections import defaultdict
from abc import ABCMeta, abstractmethod

class Error(Exception):
    """Base class for cell exceptions"""

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
        res = Defensive(self.value)
        res.stack = [*self.stack]
        return res

    def exit(self):
        """Called when evaluation returns"""
        self.stack.pop()

    @classmethod
    def enter(cls, x: object, mor: 'Mor'):
        """Called when evaluation starts"""
        if not isinstance(x, cls):
            x = cls(x)
        x.stack.append(mor)
        return x

class Obj(metaclass=ABCMeta):
    """Base class for objects (0-cells)"""
    __slots__ = ('name',)
    name: str
    defined = True
    eqs: dict['Obj', list['Eq']] = defaultdict(list)

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

        Notice that this may raise a TargetMismatch, TargetFailure...
        """
        return [
            eq for eq in self.eqs[self]
            if not eq.verify(x)
        ]

    def require_eq(self, eq: 'Eq'):
        """Associate equality `eq` to `self`"""
        self.eqs[self].append(eq)

    def __str__(self):
        if hasattr(self, 'name'):
            return self.name
        return NotImplemented

    def __repr__(self):
        return f'`type {self!s}`'

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

    def identical(self, x: 'Obj'):
        """`x` is admitted instead of `self` as source or target.

        This is possible because `self.accepts` (resp. `self.same`) is in this
        case the same function as `x.accepts` (resp. `x.same`). The converse
        does not hold in general. The preimage of `True` under `Obj.identical`
        is a reflexive and symmetric relation. The identity morphism acts as an
        isomorphism from `self` to `x`.
        """
        return self is x

    def identity(self) -> 'Mor':
        """Models morphism `category.identity`"""
        raise TypeError("Requires CategoryObj")

    @staticmethod
    def terminal() -> 'Obj':
        """Models morphism `cart.terminal`"""
        raise TypeError("Requires CartObj")

    def terminal_mor(self) -> 'Mor':
        """Models morphism `cart.terminal_mor`"""
        raise TypeError("Requires CartObj")

    def product(self, y: 'Obj') -> 'Obj':
        """Models morphism that gets source of span `cart.product`"""
        raise TypeError("Requires CartObj")

    def proj(self, name: object) -> 'Mor':
        """Projection, that is leg of product span"""
        raise TypeError("Requires Product")

class PrimObj(Obj):
    """Base of primitive objects

    Primitive objects are the ones for which the `accepts` and `same` methods
    must be defined after initialization, that is during execution of the
    theory, to which the primitive objects belong.
    """
    __slots__ = '_accepts', '_same'
    name: str
    _accepts: Callable[[object], bool]
    _same: Callable[[object, object], bool]

    def accepts(self, x: object):
        return self._accepts(x)

    def same(self, x: object, y: object):
        return self._same(x, y)

    def define(self, accepts: Callable[[object], bool], same: Callable[[object, object], bool]):
        """Set the `accepts` and `same` methods of the primitive object"""
        if self.defined:
            raise ValueError("Can't redefine primitive object")
        self._accepts = accepts
        self._same = same

    @property
    def defined(self):
        """`accepts` and `same` have been set."""
        if hasattr(self, '_accepts'):
            assert hasattr(self, '_same')
            return True
        return False

class Mor(metaclass=ABCMeta):
    """Base class for morphisms (1-cells)"""
    __slots__ = 'name', 'source', 'target'
    name: str
    source: Obj
    target: Obj
    defined = True
    defensive = False

    def _defensive_enter(self, x: object):
        return Defensive.enter(x, self)

    @abstractmethod
    def ev(self, x: object) -> object:
        """Element, to which morphism `self` maps `x`"""

    def public_ev(self, x: object):
        """Checks `x` against source before evaluation"""
        source = self.source
        if source.accepts(x):
            failed = source.failed_eqs(x)
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

    def same(self, x: 'Mor'):
        """`x` is admitted instead of `self` as ssource or starget`.

        This is possible because `self.ev` is in this case the same function as
        `x.ev`. The converse does not hold in general, and `self.target.same`
        may sometimes not return `True` when called on the result of `self.ev`
        and `x.ev`. The preimage of `True` under `Mor.same` is a reflexive and
        symmetric relation. If two morphisms are the same, then they have the
        same source (resp. target), and their equality is given by reflexivity.
        """
        # There are a few cases where one should (partially) verify the
        # signature, e.g. identity to ensure that being the same implies having
        # the same signature.
        return x is self

    def __str__(self):
        if hasattr(self, 'name'):
            return self.name
        return NotImplemented

    def __repr__(self):
        return f'`fn {self!s}: {self.source} -> {self.target}`'

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

class PrimMor(Mor):
    """Base of primitive morphisms

    Primitive morphisms are the ones for which the `ev` method must be defined
    after initialization, that is during execution of the theory, to which the
    primitive morphisms belong.
    """
    __slots__ = ('_ev', '_defensive')
    _ev: Callable[[object], object]
    _defensive: bool

    def ev(self, x: object) -> object:
        return self._ev(x)

    @property
    def defensive(self) -> bool:
        """`self` was defined with the `defensive` flag."""
        return getattr(self, '_defensive', False)

    def define(self, ev: Callable[[object], object], defensive: bool = False):
        """Set the `ev` method of the primitive morphism

        When `defensive` is `True`, the value returned by `ev` is checked
        against the target of `self` and the equalities that have this target as
        source. This dynamic type-checking is analogous to the one done with
        respect to the source of `self`, which is only always required by the
        public interface (and also includes checking equalities).
        """
        if self.defined:
            raise ValueError("Can't redefine primitive morphism")

        self._defensive = defensive
        if defensive:
            target = self.target

            @wraps(ev)
            def wrapper(x: object) -> object:
                x = self._defensive_enter(x)
                # TargetInvalid can only get caught outside the call stack, so
                # there is never a need to pop from the stack list when raising
                # such exception.

                try:
                    res = ev(x.value)
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
                            "Unable to check if there are unfulfilled "
                            "equalities", x, res,
                        ) from exc

                    if failed:
                        raise TargetFailure(
                            "Unfulfilled equalities:", x, res, failed,
                        )

                    x.exit()
                    return res
                raise TargetMismatch("Not accepted by target:", x, res)

            self._ev = wrapper
        else:
            self._ev = ev

    @property
    def defined(self):
        """`ev` has been set."""
        return hasattr(self, '_ev')

class Eq:
    """Base class for equalities (2-cells)"""
    __slots__ = 'name', 'ssource', 'starget'
    name: str
    ssource: Mor
    starget: Mor
    defined = True

    def __init__(self, ssource: Mor, starget: Mor):
        self.ssource = ssource
        self.starget = starget

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

    def parallel(self, proof: 'Eq'):
        """Equalities that coincide in their signature are parallel."""
        if proof is self:
            return True
        return (
            self.ssource == proof.ssource
            and self.starget == proof.starget
        )

    def __str__(self):
        if hasattr(self, 'name'):
            return self.name
        return NotImplemented

    def __repr__(self):
        return f'`eq {self!s}: {self.ssource} == {self.starget}`'

    def sym(self) -> 'Eq':
        """Models morphism `category.sym`"""
        raise TypeError("Requires CategoryEq")

    def trans(self, g: 'Eq') -> 'Eq':
        """Models morphism `category.trans`"""
        raise TypeError("Requires CategoryEq")

    def compose_eq(self, e: 'Eq') -> 'Eq':
        """Models morphism `category.compose_eq`"""
        raise TypeError("Requires CategoryEq")

class PrimEq(Eq):
    """Base of primitive equalities

    Primitive equalities are the ones which must be assumed (by calling method
    `define`) after initialization, that is during execution of the theory, to
    which the primitive equalities belong.
    """
    __slots__ = ('_proven',)
    name: str
    _proven: bool

    @property
    def defined(self):
        """Equality `self` has been assumed."""
        if hasattr(self, '_proven'):
            assert self._proven
            return True
        return False

    def define(self):
        """Assume equality `self`"""
        # Trusting the target of a primitive morphism is analogous to not
        # providing a proof when assuming a primitive equality.
        if self.defined:
            raise ValueError("Can't redefine primitive equality")
        self._proven = True

Cell = Obj | Mor | Eq
