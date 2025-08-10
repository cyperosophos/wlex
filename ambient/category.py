from functools import wraps
from dataclasses import dataclass

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
                Category.source(self).check(x)
            result = method(x)
            if check_target:
                Category.target(self).check(result)
            return result
            
        self._eval = wrapper
    
    def check_signature(self, value: 'Mor'):
        # With assignment and projections the source and target
        # may be undetermined. In any case, setting the source
        # should determine the target. This consists of setting
        # the source of the assignment or projection, so that
        # setting the source propagates, or is rather induced
        # from the outside.
        if Category.source(self) == Category.source(value):
            if Category.target(self) == Category.target(value):
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
        # morphisms. The return values should be True and False.
        # __eq__ should only return True in the obvious
        # cases. Other equalities must be constructed, even if
        # programmatically. Always check_signature befor
        # calling __eq__. __eq__ is extensional equality.
    def __eq__(self, x: 'Mor'):
        # This should be enough to make morphisms with different
        # signatures not equal. This is (non) equality makes sense
        # since it is definitional/extensional.
        if super().__eq__(x):
            return True
        if isinstance(x, (DefMor, DefHatMor)):
            return self == x.value
        return False

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

    def __init__(
        self, name,
        source: Mor | Obj, target: Mor | Obj,
    ):
        if isinstance(source, Mor):
            if not isinstance(target, Mor):
                hat_source = source
                source = Category.source(hat_source)
                hat_target = Category.identity(target)
        elif isinstance(target, Mor):
            hat_target = target
            target = Category.source(hat_target)
            hat_source = Category.identity(source)
            
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
        if self.hat == proof:
            self.hat_proven = True
        else:
            raise Error
        # No need to store the proof after it's checked.

    set_value = DefMor.set_value
    set_value = DefMor.eval
    set_eval = DefMor.set_eval
    __eq__ = DefMor.__eq__

class Eq:
    ssource: Mor
    starget: Mor
    proven: bool

    def __init__(self, name, ssource: Mor, starget: Mor, proof: 'Eq' | None = None):
        # No checking of globular conditions here
        self.name = name
        self._proven = False
        self.ssource = ssource
        self.starget = starget
        if proof:
            self._proven = self == proof

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
        left_side = Category.ssource(self).eval(x, check_source, check_target)
        right_side = Category.starget(self).eval(x, check_source, check_target)
        if left_side == right_side:
            return
        raise Error
    
    def __eq__(self, proof: 'Eq'):
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
    
class Comp(Mor):
    def __init__(self, f: Mor, g: Mor):
        source = Category.source(g)
        target = Category.target(f)
        super().__init__(None, source, target)
        self.f = f
        self.g = g

    def eval(self, x, check_source=True, check_target=True):
        # self is not Composable, so self.f is not a projection.
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
                return (*self.f.flat(), *self.g.flat())
            return (*self.f.flat(), self.g)
        elif isinstance(self.g, (Comp, Id)):
            return (self.f, *self.g.flat())
        else:
            return (self.f, self.g)
    
    def __eq__(self, x: Mor):
        # True should take less time.
        # True or False
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
        ssource = Category.ssource(g)
        starget = Category.starget(f)
        super().__init__(None, ssource, starget)
        self.f = f
        self.g = g
    
    @property
    def proven(self):
        return self.f.proven and self.g.proven
    
    def assume(self):
        raise Error
    # TODO: two equalities are equal if they share the same signature,
    # i.e. verify_signature returns True.
    
class CompEq(Eq):
    def __init__(self, d: Eq, e: Eq):
        self.ssource  = Category.t_compose(
            (Category.ssource(d), Category.ssource(e))
        )
        self.starget = Category.t_compose(
            (Category.starget(d), Category.starget(e))
        )
        self.d = d
        self.e = e

    @property
    def proven(self):
        return self.d.proven and self.e.proven
    
    assume = Trans.assume

class Ref(Eq):
    def __init__(self, mor: Mor):
        super().__init__(mor.name, mor, mor)
    
    @property
    def proven(self):
        return True
    
    assume = Trans.assume

class Sub:
    pass

class AttrDict(dict):
    def __init__(self, *args, **kwargs):
        super(AttrDict, self).__init__(**kwargs)
        self.__dict__ = self
        for i, arg in enumerate(args):
            self[i] = arg

    @classmethod
    def to_tuple(cls, d: 'AttrDict' | tuple | dict, tuple_cls) -> tuple:
        if isinstance(d, tuple):
            return tuple_cls(*d)
        if isinstance(d, dict):
            return tuple_cls(**d)
        i = 0
        args = []
        kwargs = d.copy()
        try:
            while True:
                args.append(kwargs.pop(i))
                i += 1
        except KeyError:
            pass
        return tuple_cls(*args, **kwargs)

@dataclass
class Path:
    f: Eq
    g: Eq

@dataclass
class Composable:
    f: Mor
    g: Mor

@dataclass
class ComposableEq:
    d: Eq
    e: Eq

@dataclass
class UniqueSource:
    d: Eq
    e: Eq

@dataclass
class AssociativitySource:
    f: Mor
    g: Mor
    h: Mor

class Category:
    def __init__(self, theory):
        self.theory = theory
        # The point of this would be to allow type checking on the overriding
        # methods of CheckedCategory. This seems to not be needed.
        # see e.g. f.source, g.target. Here type checking would be
        # superfluous as one has already checked that (f, g) is Composable.
        #self.hat_mor_cls = HatMor.cls_with_id_comp(self.identity, self.t_compose)
        self.id = UnsourcedId()

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

        # TODO: Handle compose_eq!
        
        if isinstance(g, Unsourced):
            return UnsourcedComp(f, g)

        if isinstance(f, Unsourced):
            f = f.with_source(g.target)
        return self.t_compose((f, g))

    @staticmethod
    def source(mor: Mor) -> Obj:
        return mor.source
    
    @staticmethod
    def target(mor: Mor) -> Obj:
        return mor.target
    
    @staticmethod
    def t_compose(c: Composable) -> Mor:
        # Theoretical compose
        f, g = AttrDict.to_tuple(c, Composable)
        return Comp(f, g)
    
    @staticmethod
    def identity(obj: Obj) -> Mor:
        return Id(obj)
    
    @staticmethod
    def ssource(eq: Eq) -> Mor:
        return eq.ssource
    
    @staticmethod
    def starget(eq: Eq) -> Mor:
        return eq.starget
    
    @staticmethod
    def check_obj(x: Obj) -> bool:
        return isinstance(x, Obj)
    
    @staticmethod
    def check_mor(x: Mor) -> bool:
        return isinstance(x, Mor)
    
    @staticmethod
    def check_eq(x: Eq) -> bool:
        return isinstance(x, Eq)
    
    # @staticmethod
    # def check_composable(x: Composable) -> bool:
    #     f, g = AttrDict.to_tuple(x, Composable)
    #     return (
    #         Category.check_mor(f)
    #         and Category.check_mor(g)
    #         and Category.source(f) == Category.target(g)
    #     )
    
    # @staticmethod
    # def check_path(x: Path) -> bool:
    #     f, g = AttrDict.to_tuple(x, Path)
    #     return (
    #         Category.check_eq(f)
    #         and Category.check_eq(g)
    #         and Category.ssource(f) == Category.starget(g)
    #     )
    
    @staticmethod
    def ref(mor: Mor) -> Eq:
        return Ref(mor)
    
    @staticmethod
    def trans(p: Path) -> Eq:
        f, g = AttrDict.to_tuple(p, Path)
        return Trans(f, g)
    
    #@staticmethod
    #def check_eq_unique_source(s: UniqueSource) -> bool:
    #    d, e = AttrDict.to_tuple(s, UniqueSource)
    #    return (
    #        Category.check_eq(d)
    #        and Category.check_eq(e)
    #        #and Category.
    #    )

    @staticmethod
    def eq_unique(s: UniqueSource) -> Eq:
        d, e = AttrDict.to_tuple(s, UniqueSource)
        return d
    
    @staticmethod
    def sym(eq: Eq) -> Eq:
        return eq
    
    @staticmethod
    def associativity(s: AssociativitySource) -> Eq:
        f, g, h = s
        return Category.ref(Category.t_compose(Category.t_compose(f, g), h))

    @staticmethod
    def compose_eq(s: ComposableEq):
        d, e = s
        return CompEq(d, e)

class CheckedCategory:
    backend: BCategory
    unchecked: Category

    def __init__(self, theory, backend: BCategory):
        self.unchecked = Category(theory)
        self.id = self.unchecked.id
        self.backend = backend
        u = self.unchecked
        # The backend provides only structure, no semantics.
        # backend Category is based on ambient Lex.
        # This means some of the set_check, set_eval and assume
        # is already implemented, e.g. Composable, eq, etc.
        # It makes sense then to disallow set_check, set_eval and
        # assume from the non atomic cells.
        backend.Obj.set_check(u.check_obj)
        backend.Mor.set_check(u.check_mor)
        backend.Eq.set_check(u.check_eq)
        backend.source.set_eval(u.source)
        backend.target.set_eval(u.target)
        backend.compose.set_eval(u.t_compose)
        backend.identity.set_eval(u.identity)
        backend.S.source.set_eval(u.ssource)
        backend.S.target.set_eval(u.starget)
        backend.Q.source_globular_cond.assume()
        backend.Q.target_globular_cond.assume()
        #backend.Composable.set_check(u.check_composable)
        #backend.S.S.P.Path.set_check(u.check_path)
        backend.S.S.P.ref.set_eval(u.ref)
        backend.S.S.P.trans.set_eval(u.trans)
        backend.left_identity_law.set_eval(u.ref)
        backend.right_identity_law.set_eval(u.ref)
        backend.associativity.set_eval(u.associativity)
        backend.S.S.sym.set_eval(u.sym)
        #backend.S.unique.source.set_check(u.check_eq_unique_source)
        backend.S.unique.set_eval(u.eq_unique)
        backend.compose_eq.set_eval(u.compose_eq)

    def source(self, x):
        return self.backend.source.eval(x)
    
    def target(self, x):
        return self.backend.target.eval(x)
    
    def t_compose(self, x):
        return self.backend.compose.eval(x)
    
    def mor(self, name, source: Mor | Obj, target: Mor | Obj, value=None, proof=None):
        BObj = self.backend.Obj
        BMor = self.backend.Mor
        if isinstance(source, Obj):
            BObj.check(source)
        else:
            BMor.check(source)
        if isinstance(target, Obj):
            BObj.check(target)
        else:
            BMor.check(target)
        self.unchecked.mor(name, source, target, value, proof)

    def eq(self, name, ssource: Mor | Unsourced, starget: Mor | Unsourced, proof=None):
        self.unchecked.eq(name, ssource, starget, proof)
        _eq: Eq = getattr(self.theory, name)
        BMor = self.backend.Mor
        BMor.check(_eq.ssource)
        BMor.check(_eq.starget)
        scond = self.backend.Q.source_globular_cond
        tcond = self.backend.Q.target_globular_cond
        scond.verify(_eq)
        tcond.verify(_eq)
    
# When checking e.g. Composable, it is often enough to just
# verify the equality, as applying the morphisms will check
# the source (so one does not need to check that the components
# are actually of type Mor).