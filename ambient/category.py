from functools import wraps

from ..theory.category import Category as BCategory

class Error:
    pass

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

class Mor:
    source: Obj
    target: Obj

    def __init__(
            self, name,
            source: Obj, target: Obj,
        ):
        self.name = name
        self.source = source
        self.target = target

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

        @wraps(method)
        def wrapper(x, check_source, check_target):
            if check_source:
                self.source.check(x)
            result = method(x)
            if check_target:
                self.target.check(result)
            return result
            
        self._eval = wrapper
    
    def check_signature(self, value: 'Mor'):
        # With assignment and projections the source and target
        # may be undetermined. In any case, setting the source
        # should determine the target. This consists of setting
        # the source of the assignment or projection, so that
        # setting the source propagates, or is rather induced
        # from the outside.
        if self.source == value.source:
            if self.target == value.target:
                return
            raise Error
        raise Error
        
    #def __eq__(self, x: 'Mor'):
        # Plugging equalities through transitivity without too much
        # bureaucracy requires treating some morphisms as if they
        # were equal. It also requires applying the symmetry as needed.
        # Category Mor handles assoc, left and right id, definition.
        # The first three may be handled by CompMor.__eq__.
        # One can't actually prove a negative for equality of
        # morphisms. The return values should be True and None.
        # __eq__ should only return True in the obvious
        # cases. Other equalities must be constructed, even if
        # programmatically. Always check_signature befor
        # calling __eq__.
        #pass
    def __eq__(self, x: 'Mor'):
        if super().__eq__(x):
            return True
        if isinstance(x, (DefMor, DefHatMor)):
            return self == x.value

class DefMor(Mor):
    value: 'Mor'

    def __init__(self, name, source, target, value: 'Mor' | 'Unsourced'):
        super().__init(name, source, target)
        self.set_value(value)

    def set_value(self, value, source):
        if isinstance(value, Unsourced):
            value = value.with_source(source)
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
    hat: 'Eq'
    hat_source: 'Mor'
    hat_target: 'Mor'
    hat_proven: bool

    @classmethod
    def cls_with_id_comp(cls, id, comp):
        class _Mor(cls):
            def identity(self, x):
                return id(x)
            
            def compose(self, f, g):
                return comp((f, g))   
            
    def identity(self, x):
        raise NotImplementedError
    
    def compose(self, f, g):
        raise NotImplementedError

    def __init__(
        self, name,
        source: Mor | Obj, target: Mor | Obj,
    ):
        if isinstance(source, Mor):
            if not isinstance(target, Mor):
                hat_source = source
                source = hat_source.source
                hat_target = self.identity(target)
        elif isinstance(target, Mor):
            hat_target = target
            target = hat_target.source
            hat_source = self.identity(source)
            
        target = hat_target.source
        super().__init__(name, source, target)
        self.hat_source = hat_source
        self.hat_target = hat_target
        self.hat_proven = False

    @property
    def hat(self):
        h = Eq(
            f'^{self.name}',
            self.hat_source,
            self.compose(self.hat_target, self),
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

class DefHatMor(HatMor):
    def __init__(
        self, name,
        source: Mor | Obj, target: Mor | Obj,
        value: Mor | 'Unsourced',
        proof: 'Eq',
    ):
        super().__init__(name, source, target)
        self.set_value(value, source)
        self.hat.check_proof(proof)
        self.hat_proven = True
        # No need to store the proof after it's checked.

    set_value = DefMor.set_value
    set_value = DefMor.eval
    set_eval = DefMor.set_eval
    __eq__ = DefMor.__eq__

class Eq:
    ssource: Mor
    starget: Mor
    proven: bool

    def __init__(self, name, ssource: Mor, starget: Mor, proof: 'Eq' | None):
        # No checking of globular conditions here
        self.name = name
        self._proven = False
        self.ssource = ssource
        self.starget = starget
        if proof:
            self.check_proof(proof)
            self._proven = True

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
        left_side = self.ssource.eval(x, check_source, check_target)
        right_side = self.starget.eval(x, check_source, check_target)
        if left_side == right_side:
            return
        raise Error
    
    def check_proof(self, proof: 'Eq'):
        # self.proven can't be set here as that would modify the state.
        if not proof.proven:
            raise Error
        if self.ssource == proof.ssource:
            if self.starget == proof.starget:
                return
            raise Error
        elif self.ssource == proof.starget:
            # Symmetry
            if self.starget == proof.ssource:
                return
            raise Error
        raise Error 
    
class Comp(Mor):
    def __init__(self, f: Mor, g: Mor):
        source = g.source
        target = f.target
        super().__init__(None, source, target)
        self.f = f
        self.g = g

    def eval(self, x, check_source=True, check_target=True):
        return self.f.eval(
            self.g.eval(x, check_source=check_source),
            check_source=False,
            check_target=check_target,
        )
    
    def set_eval(self, method):
        raise Error
    
    def flat(self):
        if isinstance(self.f, (Comp, Id)):
            if isinstance(self.g, (Comp, Id)):
                return [*self.f.flat(), *self.g.flat()]
            return [*self.f.flat(), self.g]
        elif isinstance(self.g, (Comp, Id)):
            return [self.f, *self.g.flat()]
    
    def __eq__(self, x: Mor):
        # True should take less time.
        if super().__eq__(x):
            return True
        if isinstance(x, (Comp, Id)):
            if self.flat() == x.flat():
                return True
    
class Id(Mor):
    def __init__(self, obj: Obj):
        super().__init__(obj.name, obj, obj)
        # Recall that eval is only called by the checked ambient.
        self.set_eval(lambda *args, **kwargs: (args, kwargs))

    def flat(self):
        return ()
    
    __eq__ = Comp.__eq__

    
class Unsourced:
    # There must be a separate class for unsourced projections, etc.
    def with_source(self, source):
        raise NotImplementedError
    
class UnsourcedComp(Unsourced):
    # Eval is not supported until converting to Comp.
    # Conversion to Comp must occur even in the absence of
    # type checking.

    def __init__(self, f, g: Unsourced):
        self.f = f
        self.g = g

    def with_source(self, source):
        return Comp(
            self.f,
            self.g.with_source(source),
        )

class UnsourcedId(Unsourced):
    # TODO: Recall that pairing can be made out of unsourced components.
    def with_source(self, source):
        return Id(source)
    
class Trans(Eq):
    def __init__(self, f: Eq, g: Eq):
        ssource = g.ssource
        starget = f.starget
        super().__init__(None, ssource, starget)
        self.f = f
        self.g = g
    
    @property
    def proven(self):
        return self.f.proven and self.g.proven
    
    def assume(self):
        raise Error
    
    def check_proof(self, proof):
        raise Error
    
    # verify_signature
    #def __eq__(self, x: Eq):
    #    return (
    #        self.ssource == x.ssource
    #        and self.starget == x.starget
    #    )
    
class CompEq(Eq):
    pass

class Ref(Eq):
    pass
    

class Sub:
    pass
    

class Category:
    def __init__(self, theory):
        self.theory = theory
        self.hat_mor_cls = HatMor.cls_with_id_comp(self.identity, self.t_compose)

    def obj(self, name):
        setattr(self.theory, name, Obj(name))

    def mor(self, name, source: Mor | Obj, target: Mor | Obj, value=None, proof=None):
        if isinstance(source, Obj) and isinstance(target, Obj):
            if proof:
                raise Error
            setattr(self.theory, name, Mor(
                name, source, target, value
            ))
        else:
            setattr(self.theory, name, self.hat_mor_cls(
                name, source, target, value, proof,
            ))

    def eq(self, name, ssource: Mor | Unsourced, starget: Mor | Unsourced, proof=None):
        if isinstance(ssource, Unsourced):
            if isinstance(starget, Unsourced):
                raise Error    
            ssource = ssource.with_source(starget.source)
        elif isinstance(starget, Unsourced):
            starget = starget.with_source(ssource.source)
        
        setattr(self.theory, name, Eq(name, ssource, starget, proof))

    def sub(self, name, theory_cls, **kw):
        setattr(self.theory, name, Sub(theory_cls, kw))

    def compose(self, head, *tail):
        if not tail:
            return head
        return self._compose(head, self.compose(*tail))
    
    def _compose(self, f: Mor | Unsourced, g: Mor | Unsourced):
        # No further type checking is or should be needed here.
        # Being Composable is the only requirement available for
        # type checking at the lang level.
        # The question arrises here about the separation between
        # type checking and evaluation (compilation time vs
        # execution time). Composing f and g does not evaluate
        # either funciton, but requires making sure (f, g) is
        # Composable. In this sense one is doing type checking
        # on f, but also on the metafunction `compose`,
        # so that at the meta level one combines type checking
        # and execution. Backend methods (source, target,
        # compose, etc.) handle type checking during execution.
        # They lack static type checking.
        
        if isinstance(g, Unsourced):
            return UnsourcedComp(f, g)

        if isinstance(f, Unsourced):
            f = f.with_source(g.target)
        return self.t_compose((f, g))

    def source(self, mor: Mor) -> Obj:
        return mor.source
    
    def target(self, mor: Mor) -> Obj:
        return mor.target
    
    def t_compose(self, c: tuple[Mor, Mor]) -> Mor:
        # Theoretical compose
        f, g = c
        return Comp(f, g)
    
    def identity(self, obj: Obj) -> Mor:
        return Id(obj)
    
class CheckedCategory(Category):
    backend: BCategory

    def __init__(self, theory, backend: BCategory):
        super().__init__(theory)
        self.backend = backend
        # The backend provides only structure, no semantics.
        backend.Obj.set_check(lambda x: isinstance(x, Obj))
        backend.Mor.set_check(lambda x: isinstance(x, Mor))
        backend.Eq.set_check(lambda x: isinstance(x, Eq))
        backend.source.set_eval(super().source)
        backend.target.set_eval(super().target)
        backend.compose.set_eval(super().t_compose)
        #backend.S.source_globular_cond.assume()

    def source(self, x):
        return self.backend.source.eval(x)
    
    def target(self, x):
        return self.backend.target.eval(x)
    
    def t_compose(self, x):
        return self.backend.compose.eval(x)
    
    def source_key(self):
        return self.backend.source
    
    def target_key(self):
        return self.backend.target
    
    def mor(self, name, source, target):
        # TODO: Handle triangle
        BObj = self.backend.Obj
        BObj.check(source)
        BObj.check(target)
        super().mor(name, source, target)
    
    def ssource_key(self):
        return self.backend.S.source
    
    def starget_key(self):
        return self.backend.S.target

    def eq(self, name, source, target):
        BMor = self.backend.Mor
        BMor.check(source)
        BMor.check(target)
        super().eq(name, source, target)
        _eq = getattr(self.theory, name)
        scond = self.backend.Q.source_globular_cond
        tcond = self.backend.Q.target_globular_cond
        scond.verify(_eq)
        tcond.verify(_eq)
    
    def _compose(self, f: Mor | Unsourced, g: Mor | Unsourced) -> Mor | Unsourced:
        h = super()._compose(f, g)
        if isinstance(h, Unsourced):
            return h
        # Convert f to Mor so that type checking can be done.
        Composable = self.backend.Composable
        Composable.check(h.f, h.g)
        return h
    
# When checking e.g. Composable, it is often enough to just
# verify the equality, as applying the morphisms will check
# the source (so one does not need to check that the components
# are actually of type Mor).