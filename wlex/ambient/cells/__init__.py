"""
Base classes for cells
"""
from functools import wraps
from typing import Optional, Union, override
from collections.abc import Callable, Sequence
from collections import defaultdict
from abc import ABCMeta, abstractmethod

class Error(Exception):
    """Base class for cell exceptions"""

class TargetInvalid(Error):
    pass

class TargetFailure(TargetInvalid):
    pass

class TargetMismatch(TargetInvalid):
    pass

class SourceInvalid(Error):
    pass

class SourceFailure(SourceInvalid):
    pass

class SourceMismatch(SourceInvalid):
    pass

class Defensive:
    """Wraps argument passed to defensive morphisms"""
    # Can't use WeakDict since the same value could have different stacks
    # according to where it's being used as argument.
    # Any cell (in)directly containing a defensive morphism is defensive,
    # so for example a morphism with a defensive source or target is defensive
    # but only for purposes of type-checking not ev. So some granularity is required.
    # When defensive comes only from source and target, there is no need for attr defensive.
    # If accepts, same, etc. raise an exception, this exception must be treated the same as
    # False under defensive checking (and also reraised).
    # So a TargetInvalid from failed_eqs will get handled (caught) by the defensive checking,
    # so there is probably no need to use defensive wrapping when calling failed_eqs, etc.
    __slots__ = 'value', 'stack'
    value: object
    stack: list[object]

    def __init__(self, value: object):
        self.value = value
        self.stack = []

class Obj(metaclass=ABCMeta):
    """Base class for objects (0-cells)"""
    __slots__ = ('name',)
    name: str
    defined = True
    defensive_accepts = False
    defensive_failed_eqs = False
    eqs: dict['Obj', list['Eq']] = defaultdict(list)

    @abstractmethod
    def accepts(self, x: object) -> bool:
        """`self` accepts `x` as element."""

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
        """Models source of span `cart.product`"""
        raise TypeError("Requires CartObj")

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
            raise ValueError("Can't redefine")
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

    @abstractmethod
    def ev(self, x: object) -> object:
        """Element, to which morphism `self` maps `x`"""

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

    def pairing_unique(self, p_eq: 'Eq', q_eq: 'Eq') -> 'Eq':
        """Models morphism `cart.pairing_unique`"""
        raise TypeError("Requires CartMor")

class PrimMor(Mor):
    """Base of primitive morphisms

    Primitive morphisms are the ones for which the `ev` method must be defined
    after initialization, that is during execution of the theory, to which the
    primitive morphisms belong.
    """
    __slots__ = ('_ev',)
    _ev: Callable[[object], object]

    def ev(self, x: object) -> object:
        return self._ev(x)

    def define(self, ev: Callable[[object], object], defensive: bool=False):
        """Set the `ev` method of the primitive morphism

        When `defensive` is `True`, the value returned by `ev` is checked
        against the target of `self` and the equalities that have this target as
        source. This dynamic type-checking is analogous to the one done with
        respect to the source of `self`, which is only always required by the
        public interface (and also includes checking equalities).
        """
        if self.defined:
            raise ValueError("Can't redefine")

        if defensive:
            target = self.target

            @wraps(ev)
            def wrapper(x: object) -> object:
                try:
                    res = ev(x)
                except Exception as exc:
                    raise TargetMismatch(f"") from exc
                if target.accepts(res):
                    failed = target.failed_eqs(res)
                    if failed:
                        raise TargetFailure(f"{x} fails equalities {failed}.")
                    return res
                raise TargetMismatch(f"{x} is not accepted by {target}.")

            self._ev = wrapper
        else:
            # TODO: wrapper must take extra arg: stack, which allows tracing
            # nested ev calls (as in compose and pairing), ev within
            # verify within failed_eqs within ev, ev with equalizer accepts, etc.
            # How does one contextualize other errors (besides target errors)?
            # Any exception raised by dev is a target error, since exceptions can't
            # be part of the type indicated by target (no Maybe monad), so doing
            # defensive ev requires catching all exceptions. Instead of passing extra
            # arg to ev, one wraps x inside a value containing the stack, this way the
            # original ev does not need to be wrapped when it's not defensive.
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
        ssource = self.ssource
        starget = self.starget
        ssource.target.same(ssource.ev(x), starget.ev(x))

    def __eq__(self, proof: object):
        # TODO: It is possible that one might just end up forgoing
        # the use of __eq__ altogether due to the mandatory object type
        # annotation, which is too lax.
        # self.proven can't be set here as that would modify the state.
        # No need for backend type checking here.
        return isinstance(proof, Eq) and self.parallel(proof)

    def __hash__(self):
        return hash(self.hint())

    def hint(self):
        # parallel in one direction
        return (self.ssource, self.starget)

    # for Obj.eql use equiv
    def parallel(self, proof: 'Eq'):
        # TODO: Symmetry has to be handled at the high-level.
        if proof is self:
            return True
        return (
            self.ssource == proof.ssource
            and self.starget == proof.starget
        )

    def weaken(self, source: Obj) -> 'Eq':
        # TODO: Too high-level
        from .cart import weaken_eq
        return weaken_eq(self, source)

    def __str__(self):
        return f'<eq_{id(self)}>'

    def __repr__(self):
        return f'`eq {self!s}: {self.ssource} == {self.starget}`'

    def sym(self) -> 'Eq':
        raise NotImplementedError

    def trans(self, g: 'Eq') -> 'Eq':
        raise NotImplementedError

    def compose_eq(self, e: 'Eq') -> 'Eq':
        raise NotImplementedError

class PrimEq(Eq):
    __slots__ = 'name', '_proven'
    name: str
    _proven: bool

    def __init__(
        self, name: str,
        ssource: Mor, starget: Mor,
    ):
        # No checking of globular conditions here
        self.name = name
        super().__init__(ssource, starget)

    @property
    def proven(self):
        return getattr(self, '_proven', False)

    def assume(self):
        # self.proven is the conjunction of the proven values of
        # all trans operands.
        if self.proven:
            raise Error
        self._proven = True

    def __str__(self):
        return self.name

class ThesisEq(Eq):
    __slots__ = 'name', 'proof'
    name: str
    proof: Eq

    def __init__(
        self, name: str,
        ssource: Mor, starget: Mor,
        proof: Eq,
    ):
        self.name = name
        super().__init__(ssource, starget)
        #source = ssource.source
        # TODO: high-level
        #proof = proof.weaken(source)
        if self.parallel(proof):
            self.proof = proof
        else:
            raise Error

    @property
    def proven(self):
        return self.proof.proven

    # @property
    # def proof(self):
    #     return self._proof.proof

    def __repr__(self):
        return f'{super().__repr__()[1:-1]} = {self.proof}'

class HatEq(Eq):
    # There is probably no point in having DefHatEq with proof property
    # since it would not be a subclass of ThesisEq.
    __slots__ = 'hat_mor',

    def __init__(self, hat_mor: Union['HatMor', 'DefHatMor']):
        ssource, starget = _hat_ssource_starget(hat_mor)
        super().__init__(ssource, starget)
        self.hat_mor = hat_mor

    @property
    def proven(self):
        return self.hat_mor.hat_proven

    def __str__(self):
        return f'^{self.hat_mor}'

class HatMor(Mor):
    __slots__ = 'name', '_eval', 'hat_source', 'hat_target', 'hat_proven'
    name: str
    _eval: Callable[[object, bool, bool], object]
    hat_source: 'Mor'
    hat_target: 'Mor'
    hat_proven: bool
    hat_eq_cls: type[HatEq] = HatEq

    def __str__(self):
        return self.name

    def __repr__(self):
        return f'`fn {self!s}: {self.hat_source} -> {self.hat_target}`'

    def __init__(
        self, name: str,
        hat_source: Mor,# | Obj,
        hat_target: Mor,# | Obj,
        #source: object,
        #target: object,
    ):
        self.name = name
        # One way to avoid redundant type checking is move all type checking (and possibly
        # identity() calls) to Category.mor. However, this makes the code more complicated.
        # TODO: Too high-level
        source, target, self.hat_source, self.hat_target = \
            _source_target_from_hat(hat_source, hat_target)
        #    _unfold_source_target(source, target)
        super().__init__(source, target)
        self.hat_proven = False

    @property
    def hat(self):
        # self.hat_proven is True only after set_eval has been called.
        return self.hat_eq_cls(self)

    def set_eval(self, method: Callable[[object], object]):
        if hasattr(self, '_eval'):
            raise Error

        peak = self.hat_source.target

        @wraps(method)
        def wrapper(
            x: object,
            check_source: bool,
            check_target: bool,
        ):
            # This will check the type of the source and target
            # Here the equality is not just assumed, it is also checked.
            # The same should happen with all assumed equalities, even if they
            # are not hat equalities? Hat equality checking is similar to type checking
            # when one sees it as indexed type checking. The way other equalities
            # are checked is ad hoc. See eq method of CheckedCategory with respect to
            # globular conditions. This justifies the call to assume.
            # Recall also that no type checking goes on in ambient Category.
            # Type checking is part of the evaluation of backend methods
            # by converting them into pointed functions (the point is the error).
            # For example, compose is dynamically checked, whereas the composed
            # functions are being statically checked. Type checking within compose
            # is part of the evaluation which produces a composed morphism.
            # Category does some type checking based on at most Cart, but since this
            # is just duck typing it can be regarded as a single type which includes
            # the point (error). This is, the default backend is a monoid.
            # CheckedCategory needs the full Lex logic in order to check
            # that source and target coincide when composing.
            # Decidable type checking implies pointed functions not just partial functions.
            # A statically type checked compose would require having proof of source
            # and target coinciding, THIS IS THE CASE with the theory Category
            # which uses Lex as its ambient, and is used as the backend of CheckedCategory.
            # The static checking of theory Category (compose) occurs when using CheckedLex.
            # The dynamic checking of theory Category occurs when using it as backend.
            # Dynamic checking is required for the atomic cells. Static checking only provides
            # guaranties for the composed cells. Notice that set_eval can't be called
            # morphisms with value, etc. Static type checking proves correctness
            # upon the assumption of correct atomic cells.
            # Eq can be true or false just like Mor gets wrapped in the Maybe monad.
            # The composed morphisms of the backend have an eval method which skips checking
            # that source and target coincide. The type checking of a composed morphism comes
            # the type checking of the atomic morphisms, which has to be dynamic.
            # By skipping, all intermediate type checking of the composition remains static on one side.
            # The backend can have composed morphisms
            # because as a theory it uses an ambient which is at least a Category.
            # If the ambient is CheckedCategory, then this ambient uses theory Category
            # as backend, which in turn uses Lex as ambient.
            # backend.compose.eval will then check that (f, g) is actually Composable.
            # This is because compose is atomic. One trusts that no static type checking
            # is needed on the backend, so the composed morphisms in the backend are assumed
            # to come from Composable. If this static type checking is needed then one uses
            # CheckedLex.
            left_side = self.hat_source.ev(x, check_source=check_source)
            result = method(x)
            right_side = self.hat_target.ev(
                result,
                check_source=check_target,
                check_target=False,
            )
            # This requires full_eq, because the type is not fixed.
            peak.equal(left_side, right_side)
            return result
            # if peak.check_eq(left_side, right_side):
            #     return result
            # raise Error

        self._eval = wrapper
        self.hat_proven = True

class DefHatMor(DefMor):
    __slots__ = 'hat_source', 'hat_target', '_hat_proof'
    hat_source: Mor
    hat_target: Mor
    _hat_proof: Eq
    hat_eq_cls: type[HatEq] = HatEq

    @property
    def hat_proven(self):
        return self._hat_proof.proven

    # @property
    # def hat_proof(self):
    #     return self._hat_proof.proof

    def __repr__(self):
        return f'`fn {self!s}: {self.hat_source} -> {self.hat_target} = {self.value}`'

    def __init__(
        self, name: str,
        hat_source: Mor,# | Obj,
        hat_target: Mor,# | Obj,
        value: Mor,# | Unsourced | Obj,
        proof: Eq,# | Mor | Obj,
    ):
        source, target, self.hat_source, self.hat_target = \
            _source_target_from_hat(hat_source, hat_target)
        #    _unfold_source_target(source, target)
        super().__init__(name, source, target, value)
        #if isinstance(proof, Obj):
        #    proof = proof.identity()
        #if isinstance(proof, Mor):
        #    proof = proof.ref()
        #hat = self._hat()
        #proof = proof.weaken(source)
        if self.hat.parallel(proof):
           self._hat_proof = proof
        else:
           raise Error

    @property
    def hat(self):
        return self.hat_eq_cls(self)

def _hat_ssource_starget(mor: HatMor | DefHatMor):
    return mor.hat_source, mor.hat_target.compose(mor)

def _unfold_source_target(source: Mor | Obj, target: Mor | Obj):
    # This is syntax not theory.
    # Some type checking of Category.mor is deferred to this method.
    # TODO: hat_weakened
    if isinstance(source, Mor):
        if isinstance(target, Mor):
            hat_target = target
            target = hat_target.source
        #elif isinstance(target, Obj):
        else:
            hat_target = target.identity()
        #else:
        #    raise TypeError
        hat_source = source
        source = hat_source.source
    elif isinstance(target, Mor):
        hat_target = target
        target = hat_target.source
        #if isinstance(source, Obj):
        hat_source = source.identity()
        #else:
        #    raise TypeError
    else:
        # Both Obj not allowed
        raise TypeError

    # There is no point in weakening. source and target are guarantied
    # to be the sources of hat_source and hat_target.
    return source, target, hat_source, hat_target