from functools import wraps
from typing import Optional

class Error(Exception):
    pass

class Obj:
    __slots__ = ()

    def check(self, x):
        raise NotImplementedError

    def set_check(self, method):
        raise Error

    def identity(self):
        from ..ambient.category import Id
        return Id(self)
    
    def terminal_mor(self):
        from ..ambient.cart import TerminalMor
        return TerminalMor(self)
    
    def product(self, y):
        from ..ambient.cart import Span
        x = self
        source = Obj()
        return Span(Mor(source, x), Mor(source, y))
    
    def check_eq(self, x, y):
        raise NotImplementedError

class PrimObj(Obj):
    __slots__ = '_check', '_check_eq'

    def __init__(self, name):
        # An object can't be assigned a value like a morphism can.
        # This is because all objects have the same signature,
        # i.e. type, so the assignment would be superfluous.
        # The Limit class provides a check method, analogous to
        # the way the Comp class provides an eval method.
        self.name = name

        def _check(x):
            raise Error
        
        def _check_eq(x, y):
            raise Error
        
        self._check = _check
        self._check_eq = _check_eq
        # TODO: Do something similar in PrimMor and PrimEq.

    def check(self, x):
        self._check(x)
    
    def set_check(self, method):
        @wraps(method)
        def wrapper(x):
            if method(x):
                return
            raise Error

        self._check = wrapper

    def check_eq(self, x, y):
        return self._check_eq(x, y)
    
    def set_check_eq(self, method):
        @wraps(method)
        def wrapper(x, y):
            if method(x, y):
                return
            raise Error
    
    def __str__(self):
        return self.name

    def __repr__(self):
        return f'`type {self!s}`'

class Unsourced:
    __slots__ = ()

    # There must be a separate class for unsourced projections, etc.
    def with_source(self, source: Obj) -> 'Mor':
        raise NotImplementedError
    
class Mor:
    __slots__ = 'source', 'target'

    hat: 'Eq'
    source: Obj
    target: Obj

    def eval(self, x, check_source=True, check_target=True):
        raise NotImplementedError

    def set_eval(self, method):
        raise Error
    
    def __init__(self, source: Obj, target: Obj):
        # Type checking from syntax not backend.
        # Most type checking should be done at the public method
        # in order to avoid redundant type checking.
        self.source = source
        self.target = target

    @property
    def hat(self):
        # At least in the case of Cart this could be the
        # triangle involving the terminal object.
        # It is better in fact to just raise an Error.
        raise Error

    def ref(self):
        from ..ambient.category import Ref
        return Ref(self)
    
    def comp(self, g):
        from ..ambient.category import Comp
        f = self
        return Comp(f, g)
    
    def terminal_mor_unique(self):
        # Just like with comp, we don't check the equalizer.
        from ..ambient.cart import TerminalMorUnique
        return TerminalMorUnique(self)
    
    def pairing(self, q: 'Mor'):
        # TODO: Should signature type hints only be used when there is
        # no type checking in the body?
        from ..ambient.cart import ProductMor
        p = self
        # TODO: Notice how one needs type conversion from ProductMor
        # to Span. For Mor this is supported as a projection.
        # The way to go is to compose with Span (or Mor), i.e. the identity,
        # or any morphism with an appropriate source. This means that
        # Category.compose has to be overridden in Cart, so that this sort of
        # type conversion is inserted where the types don't match.
        # Actually a more appropriate approach is to adjust the type
        # checking of products so that they follow duck typing.
        # This is possible with products within products, like
        # Span within ProductMor. Recall that backend type checking
        # does not compare types, it uses the check method of the type
        # which in the simplest cases calls `isinstance`.
        # A simpler way to deal with this is to use inheritance, even if
        # it is used in an ad hoc manner. This works for backend type checking
        # and for the methods of the unchecked ambient.
        # The remaining type checking to be fixed is the one of t_compose.
        # Here t_compose has to be precomposed with a morphism
        # DuckComposable -> Composable. This simply requires (internally)
        # precomposing f (in the parameters f, g of t_compose) with a type
        # conversion, so that in effect one changes the source of f.
        # Cf. weakening rule in cartesian multicategory.
        # There is some reduntant type checking involved here.
        # We have to check that the types are compatible when they are not equal.
        # Something analogous occurs with coprojections.
        # Some mixins of types through products may be difficult to
        # replicate using inheritance, etc.
        # TODO: Remember to handle param projections and assigments,
        # which allow having local variables. Check other notes!
        return ProductMor(p, q)
    
    #def __eq__(self, x: 'Mor'):
        # Plugging equalities through transitivity without too much
        # bureaucracy requires treating some morphisms as if they
        # were equal. It also requires applying the symmetry as needed.
        # Category Mor handles assoc, left and right id, definition.
        # The first three may be handled by CompMor.__eq__.
        # One can't actually prove a negative for equality of
        # morphisms. The return values should be True and False.
        # __eq__ should only return True in the obvious
        # cases. Other equalities must be constructed, even if
        # programmatically. Always check_signature before
        # calling __eq__. __eq__ is extensional equality.
    def __eq__(self, x: 'Mor'):
        # TODO: Unit tests must check that __eq__ is an equiv rel.
        # This should be enough to make morphisms with different
        # signatures not equal. This (non) equality makes sense
        # since it is definitional/extensional.
        # There are a few cases where one should verify the signature,
        # e.g. identity.
        from .category import Comp
        if x is self:
            return True
        if isinstance(x, DefMor):
            return self == x.value
        elif not isinstance(self, Comp) and isinstance(x, Comp):
            # Defer to Comp.__eq__.
            # This is especially useful in the case of p_eq, q_eq of pairing.
            return x.__eq__(self)
        elif not isinstance(x, Mor):
            raise TypeError
        return False
    
    def check_signature(self, value: 'Mor'):
        # With assignment and projections the source and target
        # may be undetermined. In any case, setting the source
        # should determine the target. This consists of setting
        # the source of the assignment or projection, so that
        # setting the source propagates, or is rather induced
        # from the outside.

        if not isinstance(value, Mor):
            # TypeError because this is not backend type checking
            raise TypeError

        if self.source == value.source:
            if self.target == value.target:
                return
            raise Error(f'Targets of {self!r} and {value!r} differ')
        raise Error(f'Sources of {self!r} and {value!r} differ')

    def weakened(self, source: 'Obj') -> 'Mor':
        # TODO: The weakening flag must only be in the ambient and then
        # be passed as an argument to methods of other classes.
        from .cart import weakened_mor
        return weakened_mor(self, source)

class PrimMor(Mor):
    __slots__ = 'name', '_eval'

    def __init__(self, name, source: Obj, target: Obj,):
        self.name = name
        super().__init__(source, target)

    __str__ = PrimObj.__str__

    def __repr__(self):
        return f'`fn {self!s}: {self.source} -> {self.target}`'

    def eval(self, x, check_source=True, check_target=True):
        return self._eval(x, check_source, check_target)

    def set_eval(self, method):
        if hasattr(self, '_eval'):
            raise Error
        # We don't use Category.source, because no type checking
        # is required here. A priori, self is a Mor and self.source
        # is an object (as checked in CheckedCategory.mor).
        # We assume this is called as an instance method.
        # CheckedCategory.mor (and CheckedCategory.eq, etc.) do
        # a sort of ad hoc type checking to ensure that some equalities
        # (e.g. glob cond) can be assumed and that certain morphisms
        # (like source, target) are semi-prechecked, i.e. they need only
        # be checked with check_source=True and check_target=False.
        # However we accept having redundant type checking, as we can't
        # assume algorithm of Category.source, Category.target.
        # Methods such as set_eval which don't come from the theory
        # should not include any backend type checking.
        # Backend type checking should occur only with methods
        # that are called when defining a theory (e.g. compose).
        # set_eval is not used when defining a theory but when
        # setting the semantics of the backend.
        # What about check_signature?
        # We may check that method here is of the right type, but that
        # is just to fail early with a TypeError.
        # Backend type checking in set_eval seems pointless.
        source = self.source
        target = self.target

        @wraps(method)
        def wrapper(x, check_source, check_target):
            if check_source:
                source.check(x)
            result = method(x)
            if check_target:
                target.check(result)
            return result
            
        self._eval = wrapper

class DefMor(Mor):
    __slots__ = 'name', 'value'
    value: Mor

    __str__ = PrimObj.__str__

    def __repr__(self):
        return f'`fn {self!s}: {self.source} -> {self.target} = {self.value}`'

    def __init__(self, name, source, target, value: Mor | Unsourced | Obj, weakened=False):
        self.name = name
        super().__init__(source, target)
        if weakened:
            value = value.weakened(source)
        self._set_value(value, source)

    def _set_value(self, value, source):
        # Making sure the signature of value is correct is not part of the theory.
        # From the perspective of the theory there is only one morphism.
        # The two morphisms that are syntactically distinguished (Mor and DefMor)
        # are extensionally equal.
        # check_signature is not backend type checked, but it does check
        # that value is a Mor etc. as required in order for the value assignment
        # to make sense.
        # Interpreting Obj value as morphism is also part of the syntax not of the theory.

        if isinstance(value, Unsourced):
            value = value.with_source(source)
        elif isinstance(value, Obj):
            value = value.identity()
        self.check_signature(value)
        self.value = value

    def eval(self, x, check_source=True, check_target=True):
        return self.value.eval(x, check_source, check_target)
    
    def __eq__(self, x: Mor):
        if super().__eq__(x):
            return True
        if isinstance(x, (DefMor, DefHatMor)):
            return self.value == x.value
        return self.value == x

class HatMor(Mor):
    __slots__ = 'name', 'hat_source', 'hat_target', 'hat_proven'
    hat_source: 'Mor'
    hat_target: 'Mor'
    hat_proven: bool

    __str__ = PrimObj.__str__

    def __repr__(self):
        return f'`fn {self!s}: {self.hat_source} -> {self.hat_target}`'

    def __init__(
        self, name,
        source: Mor | Obj,
        target: Mor | Obj,
    ):
        self.name = name
        # One way to avoid redundant type checking is move all type checking (and possibly
        # identity() calls) to Category.mor. However, this makes the code more complicated.
        source, target, self.hat_source, self.hat_target = \
            self.unfold_source_target(source, target)
        super().__init__(name, source, target)
        self.hat_proven = False

    @staticmethod
    def unfold_source_target(source, target):
        # This is syntax not theory.
        # Some type checking of Category.mor is deferred to this method.

        if isinstance(source, Mor):
            if isinstance(target, Mor):
                hat_target = target
                target = hat_target.source
            elif isinstance(target, Obj):
                hat_target = target.identity()
            else:
                raise TypeError
            hat_source = source
            source = hat_source.source
        elif isinstance(target, Mor):
            hat_target = target
            target = hat_target.source
            if isinstance(source, Obj):
                hat_source = source.identity()
            else:
                raise TypeError
        else:
            raise TypeError

        return source, target, hat_source, hat_target

    @property
    def hat(self):
        h = Eq(
            f'^{self.name}',
            self.hat_source,
            self.hat_target.comp(self),
        )
        if self.hat_proven:
            h.assume()
        return h

    def set_eval(self, method):
        if hasattr(self, '_eval'):
            raise Error
        
        peak = self.hat_source.target

        @wraps(method)
        def wrapper(x, check_source, check_target):
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
            left_side = self.hat_source.eval(x, check_source=check_source)
            result = method(x)
            right_side = self.hat_target.eval(
                result,
                check_source=check_target,
                check_target=False,
            )
            # This requires full_eq, because the type is not fixed.
            peak.check_eq(left_side, right_side)
            return result
            # if peak.check_eq(left_side, right_side):
            #     return result
            # raise Error
            
        self._eval = wrapper
        self.hat_proven = True

class Eq:
    __slots__ = 'ssource', 'starget', '_proven'
    ssource: Mor
    starget: Mor
    _antecedent = None
    _proven = False

    def __init__(self, ssource: Mor, starget: Mor, proof: Optional['Eq'] = None, weakened=False):
        # No checking of globular conditions here
        self.ssource = ssource
        self.starget = starget
        # Notice that __eq__ is not affected by weakening.
        if proof:
            # Notice that with weaking some errors get raised earlier,
            # there more as syntax errors than as type checking errors.
            if not isinstance(proof, Eq):
                raise TypeError
            if weakened:
                if self._eq(
                    proof.ssource.weakened(ssource),
                    proof.starget.weakened(ssource),
                ):
                    self._antecedent = proof
                else:
                    raise Error
            elif self == proof:
                self._antecedent = proof
            else:
                # Invalid proof
                raise Error

    def proven(self) -> bool:
        # This can change. For example f can be assumed after instantiation
        # Trans. Hence a property not an attribute.
        if self._proven:
            return True
        ant = self._antecedent
        if ant:
            return ant.proven()
        return False
    
    def antecedent(self) -> Optional['Eq']:
        if self._proven:
            return self
        ant = self._antecedent
        if ant:
            return ant.antecedent()
    
    def assume(self):
        raise Error
    
    def verify(self, x, check_source=True, check_target=True):
        left_side = self.ssource.eval(x, check_source, check_target)
        right_side = self.starget.eval(x, check_source, check_target)
        if left_side == right_side:
            return
        raise Error
    
    def __eq__(self, proof: 'Eq'):
        if proof is self:
            return True
        if not isinstance(proof, Eq):
            raise TypeError
        # self.proven can't be set here as that would modify the state.
        # No need for backend type checking here.
        return self._eq(proof.ssource, proof.starget)

    def _eq(self, ssource, starget):
        if self.ssource == ssource:
            if self.starget == starget:
                return True
            return False
        elif self.ssource == starget:
            # Symmetry
            if self.starget == ssource:
                return True
            return False
        return False
    
    def weakened(self, source: 'Obj') -> 'Eq':
        return Eq(
            self.ssource.weakened(source),
            self.starget.weakened(source),
            self,
            weakened=True,
        )
    
    def trans(self, g):
        from ..ambient.category import Trans
        return Trans(self, g)
    
    def comp_eq(self, e):
        from ..ambient.category import CompEq
        return CompEq(self, e)
    
class PrimEq(Eq):
    __slots__ = 'name',

    def __init__(self, name, ssource: Mor, starget: Mor, proof: Optional['Eq'] = None):
        # No checking of globular conditions here
        self.name = name
        super().__init__(ssource, starget, proof)

    def assume(self):
        # self.proven is the conjunction of the proven values of
        # all trans operands.
        if self._antecedent:
            raise Error
        if self._proven:
            raise Error
        self._proven = True

    __str__ = PrimObj.__str__

    def __repr__(self):
        return f'`eq {self!s}: {self.ssource} == {self.starget} = {self._proven}`'

class DefHatMor(DefMor):
    __slots__ = 'hat_source', 'hat_target', 'hat_proven'
    hat_source: 'Mor'
    hat_target: 'Mor'
    hat_proven: bool

    def __repr__(self):
        return f'`fn {self!s}: {self.hat_source} -> {self.hat_target} = {self.value}`' 

    def __init__(
        self, name,
        source: Mor | Obj, target: Mor | Obj,
        value: Mor | Unsourced | Obj,
        proof: Eq | Mor | Obj,
        weakened=False,
    ):
        source, target, self.hat_source, self.hat_target = \
            HatMor.unfold_source_target(source, target)
        super().__init__(name, source, target, value, weakened)
        if isinstance(proof, Obj):
            proof = proof.identity()
        if isinstance(proof, Mor):
            proof = proof.ref()
        self.hat_proven = False
        if self.hat == proof:
            self.hat_proven = proof.proven()
        else:
            raise Error
        # No need to store the proof after it's checked.

    hat = HatMor.hat