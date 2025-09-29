from functools import wraps
from typing import Optional

class Error(Exception):
    pass

def filter_name(name):
    return name or '<anon>'

_an = filter_name

class Obj:
    def __init__(self, name):
        # An object can't be assigned a value like a morphism can.
        # This is because all objects have the same signature,
        # i.e. type, so the assignment would be superfluous.
        # The Limit class provides a check method, analogous to
        # the way the Comp class provides an eval method.
        self.name = name

    def check(self, x):
        self._check(x)
    
    def set_check(self, method):
        @wraps(method)
        def wrapper(x):
            if method(x):
                return
            raise Error

        self._check = wrapper

    def identity(self):
        from ..ambient.category import Id
        return Id(self)

    def __str__(self):
        return f'{_an(self.name)}'
    
    def __repr__(self):
        return f'`type {_an(self.name)}`'

class Unsourced:
    # There must be a separate class for unsourced projections, etc.
    def with_source(self, source):
        raise NotImplementedError

class Mor:
    hat: 'Eq'
    source: Obj
    target: Obj

    def __init__(
            self, name,
            source: Obj, target: Obj,
        ):
        self.name = name
        self.source = source # check type??
        self.target = target

    __str__ = Obj.__str__
    
    def __repr__(self):
        return f'`fn {_an(self.name)}: {_an(self.source.name)} -> {_an(self.target.name)}`'

    @property
    def hat(self):
        # At least in the case of Cart this could be the
        # triangle involving the terminal object.
        # It is better in fact to just raise an Error.
        raise Error

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
    
    def check_signature(self, value: 'Mor'):
        # With assignment and projections the source and target
        # may be undetermined. In any case, setting the source
        # should determine the target. This consists of setting
        # the source of the assignment or projection, so that
        # setting the source propagates, or is rather induced
        # from the outside.

        if not isinstance(value, Mor):
            raise Error

        if self.source == value.source:
            if self.target == value.target:
                return
            raise Error(f'Targets of {self} and {value} differ')
        raise Error(f'Sources of {self} and {value} differ')
        
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
        # This should be enough to make morphisms with different
        # signatures not equal. This (non) equality makes sense
        # since it is definitional/extensional.
        # There are a few cases where one should verify the signature,
        # e.g. identity.
        if x is self:
            return True
        if isinstance(x, (DefMor, DefHatMor)):
            return self == x.value
        return False

class DefMor(Mor):
    value: Mor

    def __init__(self, name, source, target, value: Mor | Unsourced | Obj):
        super().__init__(name, source, target)
        self.set_value(value, source)

    def set_value(self, value, source):
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
    
    def set_eval(self, method):
        raise Error
    
    def __eq__(self, x: Mor):
        if super().__eq__(x):
            return True
        if isinstance(x, (DefMor, DefHatMor)):
            return self.value == x.value
        return self.value == x

class HatMor(Mor):
    hat_source: 'Mor'
    hat_target: 'Mor'
    hat_proven: bool

    def __init__(
        self, name,
        source: Mor | Obj,
        target: Mor | Obj,
    ):
        # TODO: Check type of source, target here instead of in CheckedCategory.mor?
        # One way to avoid redundant type checking is move all type checking (and possibly
        # identity() calls) to Category.mor.
        source, target, self.hat_source, self.hat_target = \
            self.unfold_source_target(source, target)
        super().__init__(name, source, target)
        self.hat_proven = False

    @staticmethod
    def unfold_source_target(source, target):
        # This is syntax not theory.

        if isinstance(source, Mor):
            if isinstance(target, Mor):
                hat_target = target
                target = hat_target.source
            elif isinstance(target, Obj):
                hat_target = target.identity()
            else:
                raise Error
            hat_source = source
            source = hat_source.source
        elif isinstance(target, Mor):
            hat_target = target
            target = hat_target.source
            if isinstance(source, Obj):
                hat_source = source.identity()
            else:
                raise Error

        return source, target, hat_source, hat_target

    @property
    def hat(self):
        from ..ambient.category import Category

        h = Eq(
            f'^{self.name}',
            self.hat_source,
            Category.t_compose((self.hat_target, self)),
        )
        if self.hat_proven:
            h.assume()
        return h

    def set_eval(self, method):
        if hasattr(self, '_eval'):
            raise Error

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
            if left_side == right_side:
                return result
            raise Error
            
        self._eval = wrapper
        self.hat_proven = True

class Eq:
    ssource: Mor
    starget: Mor
    proven: bool

    def __init__(self, name, ssource: Mor, starget: Mor, proof: Optional['Eq'] = None):
        # No checking of globular conditions here
        self.name = name
        self._proven = False
        self.ssource = ssource
        self.starget = starget
        if proof and self == proof:
            self._proven = proof.proven

    @property
    def proven(self):
        return self._proven

    def assume(self):
        # self.proven is the conjunction of the proven values of
        # all trans operands.
        if self._proven:
            raise Error
        self._proven = True

    def verify(self, x, check_source=True, check_target=True):
        from ..ambient.category import Category

        left_side = Category.ssource(self).eval(x, check_source, check_target)
        right_side = Category.starget(self).eval(x, check_source, check_target)
        if left_side == right_side:
            return
        raise Error
    
    def __eq__(self, proof: 'Eq'):
        from ..ambient.category import Category

        if proof is self:
            return True
        # self.proven can't be set here as that would modify the state.
        if Category.ssource(self) == Category.ssource(proof):
            if Category.starget(self) == Category.starget(proof):
                return True
            return False
        elif Category.ssource(self) == Category.starget(proof):
            # Symmetry
            if Category.starget(self) == Category.ssource(proof):
                return True
            return False
        return False
    
    __str__ = Obj.__str__
    
    def __repr__(self):
        return f'`eq {_an(self.name)}: {_an(self.ssource.name)} == {_an(self.starget.name)}`'

class DefHatMor(DefMor):
    hat_source: 'Mor'
    hat_target: 'Mor'
    hat_proven: bool    

    def __init__(
        self, name,
        source: Mor | Obj, target: Mor | Obj,
        value: Mor | Unsourced | Obj,
        proof: Eq | Mor | Obj,
    ):
        from ..ambient.category import Category

        source, target, self.hat_source, self.hat_target = \
            HatMor.unfold_source_target(source, target)
        super().__init__(name, source, target, value)
        if isinstance(proof, Obj):
            proof = Category.identity(proof)
        if isinstance(proof, Mor):
            proof = Category.ref(proof)
        self.hat_proven = False
        if self.hat == proof:
            self.hat_proven = proof.proven
        else:
            raise Error
        # No need to store the proof after it's checked.

    hat = HatMor.hat
    #set_value = DefMor.set_value
    #eval = DefMor.eval
    #set_eval = DefMor.set_eval
    #__eq__ = DefMor.__eq__