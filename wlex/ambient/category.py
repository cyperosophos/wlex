from functools import wraps
from dataclasses import dataclass
import weakref

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
    hat: 'Eq'
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
        # signatures not equal. This (non) equality makes sense
        # since it is definitional/extensional.
        # There are a few cases where one should verify the signature,
        # e.g. identity.
        if super().__eq__(x):
            return True
        if isinstance(x, (DefMor, DefHatMor)):
            return self == x.value
        return False

class DefMor(Mor):
    value: 'Mor'

    def __init__(self, name, source, target, value: 'Mor' | 'Unsourced' | 'Obj'):
        super().__init(name, source, target)
        self.set_value(value)

    def set_value(self, value, source):
        if isinstance(value, Unsourced):
            value = value.with_source(source)
        elif isinstance(value, Obj):
            value = Category.identity(value)
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

class DefHatMor(HatMor):
    def __init__(
        self, name,
        source: Mor | Obj, target: Mor | Obj,
        value: Mor | 'Unsourced' | 'Obj',
        proof: 'Eq' | Mor | Obj,
    ):
        super().__init__(name, source, target)
        self.set_value(value, source)
        if isinstance(proof, Obj):
            proof = Category.identity(proof)
        if isinstance(proof, Mor):
            proof = Category.ref(proof)
        if self.hat == proof:
            self.hat_proven = True
        else:
            raise Error
        # No need to store the proof after it's checked.

    set_value = DefMor.set_value
    eval = DefMor.eval
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
        if proof and self == proof:
            self._proven = proof._proven

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
        if super().__eq__(proof):
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
    
    def __eq__(self, x: Mor):
        return (
            Comp.__eq__(self, x)
            and Category.source(self) == Category.source(x)
        )
    
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
    
@staticmethod
def _extract_sub_kw(kw: dict):
    sub_kw = dict()
    key: str
    for key in kw:
        skey = key.split('.', 1)
        if len(skey) > 1:
            d = dict()
            sub_kw[skey[0]] = d
            d[skey[1]] = kw.pop(key)
    return sub_kw

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
        if not isinstance(d, AttrDict):
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

def variadic(m):
    wraps(m)
    def wrapper(head, *tail):
        if not tail:
            return head
        return m(head, wrapper(*tail))
    return wrapper

class Composer:
    @classmethod
    def compose(cls, f: Mor | Unsourced | Eq | Obj, g: Mor | Unsourced | Eq | Obj) -> Mor | Unsourced | Eq:
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

        f, g = (
            Category.identity(m) if isinstance(m, Obj) else m
            for m in (f, g)
        )

        # Unsourced, Eq comp is allowed but not Eq, Unsourced. 
        if isinstance(g, Unsourced):
            if isinstance(f, Eq):
                raise Error
            return UnsourcedComp(f, g)

        if isinstance(f, Unsourced):
            if isinstance(g, Eq):
                # No checking needed with ref
                f = Category.ref(f.with_source(g.ssource.target))
                return cls.compose_eq((f, g))
            f = f.with_source(g.target)
            return cls.t_compose((f, g))

        if isinstance(f, Eq):
            if isinstance(g, Mor):
                g = Category.ref(g)
            return cls.compose_eq((f, g))
        
        if isinstance(g, Eq):
            f = Category.ref(f)
            return cls.compose_eq((f, g))
        
        return cls.t_compose((f, g))
    
    @staticmethod
    def t_compose(c: Composable) -> Mor:
        raise NotImplementedError
    
    @staticmethod
    def compose_eq(c: ComposableEq) -> Eq:
        raise NotImplementedError
    
class Transer:
    @classmethod
    def trans(cls, f: Eq | Mor | Obj, g: Eq | Mor | Obj) -> Eq:
        # Handle identity
        f, g = (
            Category.ref(Category.identity(m)) if isinstance(m, Obj) else
            (Category.ref(m) if isinstance(m, Mor) else m)
            for m in (f, g)
        )
        return cls.t_trans((f, g))
    
    @staticmethod
    def t_trans(p: Path) -> Eq:
        raise NotImplementedError

class Category:
    def __init__(self, theory, name='', kw=None, sub_kw=None, theory_clss=None):
        # The point of this would be to allow type checking on the overriding
        # methods of CheckedCategory. This seems to not be needed.
        # see e.g. f.source, g.target. Here type checking would be
        # superfluous as one has already checked that (f, g) is Composable.
        #self.hat_mor_cls = HatMor.cls_with_id_comp(self.identity, self.t_compose)
        self.id = UnsourcedId()
        self.kw = kw or dict()
        self.sub_kw = sub_kw or dict()
        self.name = name
        self.theory_clss = theory_clss or ()
        self.theory = weakref.proxy(theory)

    def with_kw(self, theory, name, theory_clss, kw, sub_kw):
        # This needs to handle kw used buy sub at lower levels.
        # e.g. S.P.Q in line 35 of theory/category.py.
        # TODO: An important goal is to be able to define monads,
        # hence natural transformations. This requires making mor
        # support self and self.T within the __init__ of the theory
        # as if they were functors.
        # Inheritance requires this to be a classmethod.

        return Category(theory, name, theory_clss, kw, sub_kw)

    def obj(self, name):
        theory = self.theory
        if name in self.kw:
            setattr(theory, name, self.kw[name])
        else:
            setattr(theory, name, Obj(self.cell_name(name)))

    def mor(
            self, name,
            source: Mor | Obj,
            target: Mor | Obj,
            value: Mor | Unsourced | Obj | None = None,
            proof: Eq | Mor | Obj | None = None
        ):
        # Morphisms with value can't be overridden by kw.
        # sub corresponds to a functor, so saying f = g h
        # and then F(f) = k is backwards, because F(f) is already
        # defined as F(g) F(h).
        # One checks the signature (source, target args).
        # In the case of HatMor, one must also check the hat.
        # This does not mean that one should also handle value and proof.
        # The overridden mor keeps its name (this is different from Obj)
        # it simply gets replaced by a DefMor or DefHatMor with the
        # overriding mor as value.
        theory = self.theory
        if name in self.kw:
            if value or proof:
                raise Error
            # The purpose of setting the value indirectly is to check signature.
            value = self.kw[name]

        if isinstance(source, Obj) and isinstance(target, Obj):
            if proof:
                raise Error
            if value:
                setattr(theory, name, DefMor(
                    self.cell_name(name),
                    source, target, value,
                ))
            else:
                setattr(theory, name, Mor(
                    self.cell_name(name),
                    source, target,
                ))
        elif value:
            if not proof:
                proof = value.hat
            setattr(theory, name, DefHatMor(
                self.cell_name(name),
                source, target, value, proof,
            ))
        else:
            setattr(theory, name, HatMor(
                self.cell_name(name),
                source, target,
            ))

    def eq(
            self, name,
            ssource: Mor | Unsourced | Obj,
            starget: Mor | Unsourced | Obj,
            proof: 'Eq' | Mor | Obj = None,
        ):
        theory = self.theory
        if name in self.kw:
            if proof:
                raise Error
            proof = self.kw[name]

        ssource, starget = (
            Category.identity(m) if isinstance(m, Obj) else m
            for m in (ssource, starget)
        )
        
        if isinstance(ssource, Unsourced):
            if isinstance(starget, Unsourced):
                raise Error    
            ssource = ssource.with_source(starget.source)
        elif isinstance(starget, Unsourced):
            starget = starget.with_source(ssource.source)

        if isinstance(proof, Obj):
            proof = Category.identity(proof)
        if isinstance(proof, Mor):
            proof = Category.ref(proof)
        
        setattr(theory, name, Eq(self.cell_name(name), ssource, starget, proof))

    def sub(self, name, theory_cls, **kw):
        # If both self.sub_kw and kw override cells then an error
        # occurs, because what should have happened is that the overriding
        # cell got overridden. This applies to sub_kw as well.
        # kw gets separated into kw and sub_kw.
        # sub_kw is a dict with kw values used for the sub's
        # within the sub.
        # Only cells with no value (atomic cells) can be overridden.
        # These cells are created and set using obj, mor, eq, sub,
        # hence these methods handle the process of overriding.
        theory = self.theory
        if name in self.kw:
            if kw:
                # Can't override partially defined functor.
                # Must instead override missing components.
                raise Error
            if self.sub_kw.get(name):
                # Can't be overriden by sub_kw when overridden by kw.
                raise Error
            # This is wrong because kw must include all attributes.
            #kw = _sub.get_kw(self, theory_cls)
            # theory_cls has to coincide.
            _sub = self.kw[name]
            if isinstance(_sub, theory_cls):
                setattr(theory, name, _sub)
            else:
                raise Error
            return

        super_kw: dict = self.sub_kw[name]
        for key, value in super_kw.items():
            if key in kw:
                raise Error
            kw[key] = value

        sub_kw = _extract_sub_kw(kw)
        #setattr(theory, name, Sub(name, self, theory_cls, kw, sub_kw))
        # Avoid circular class instantiation
        theory_clss = (*self.theory_clss, type(theory))
        for tc in theory_clss:
            if theory_cls is tc:
                raise Error
        sub_name = self.cell_name(name)
        setattr(
            theory, name,
            theory_cls(lambda th: self.with_kw(th, sub_name, kw, sub_kw, theory_clss)),
        )

    def cell_name(self, name):
        if not self.name:
            return name
        return f'{self.name}.{name}'

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
    
    @staticmethod
    def ref(mor: Mor) -> Eq:
        return Ref(mor)
    
    @staticmethod
    def t_trans(p: Path) -> Eq:
        f, g = AttrDict.to_tuple(p, Path)
        return Trans(f, g)

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
    def compose_eq(c: ComposableEq):
        d, e = c
        return CompEq(d, e)
    
    class _Composer(Composer):
        @staticmethod
        def t_compose(c):
            return Category.t_compose(c)
        
        @staticmethod
        def compose_eq(c):
            return Category.compose_eq(c)
        
    class _Transer(Transer):
        @staticmethod
        def t_trans(p):
            return Category.t_trans(p)
        
    compose = variadic(Composer.compose)
    trans = variadic(Transer.trans)

class CheckedCategory:
    backend: BCategory
    unchecked: Category

    def __init__(self, theory, backend: BCategory, name='', kw=None, sub_kw=None, theory_clss=None):
        # Notice that type checking only needs to be done the first
        # time theory_cls is instantiated when there is no sub overriding.
        self.unchecked = Category(theory, name, kw, sub_kw, theory_clss)
        self.id = self.unchecked.id
        self.backend = backend

    def set_semantics(self, backend: BCategory):
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
        backend.S.S.P.trans.set_eval(u.t_trans)
        backend.left_identity_law.set_eval(u.ref)
        backend.right_identity_law.set_eval(u.ref)
        backend.associativity.set_eval(u.associativity)
        backend.S.S.sym.set_eval(u.sym)
        #backend.S.unique.source.set_check(u.check_eq_unique_source)
        backend.S.unique.set_eval(u.eq_unique)
        backend.compose_eq.set_eval(u.compose_eq)

        # TODO: Should there be a way to check that the whole backend
        # has semantics, i.e. set_check, set_eval and assume has been
        # called on all atomic cells.

    def with_kw(self, theory, name, kw, sub_kw, theory_clss):
        return CheckedCategory(theory, self.backend, name, kw, sub_kw, theory_clss)

    def source(self, x):
        return self.backend.source.eval(x)
    
    def target(self, x):
        return self.backend.target.eval(x)
    
    def t_compose(self, x):
        return self.backend.compose.eval(x)
    
    def identity(self, x):
        return self.backend.identity.eval(x)
    
    def ssource(self, x):
        return self.backend.S.source.eval(x)
    
    def starget(self, x):
        return self.backend.S.target.eval(x)
    
    def ref(self, x):
        return self.backend.S.S.P.ref.eval(x)
    
    def t_trans(self, x):
        return self.backend.S.S.P.trans.eval(x)
    
    def left_identity_law(self, x):
        return self.backend.left_identity_law.eval(x)
    
    def right_identity_law(self, x):
        return self.backend.right_identity_law.eval(x)
    
    def associativity(self, x):
        return self.backend.associativity.eval(x)
    
    def sym(self, x):
        return self.backend.S.S.sym.eval(x)
    
    def unique(self, x):
        return self.backend.S.unique.eval(x)
    
    def compose_eq(self, x):
        return self.backend.compose_eq.eval(x)
    
    def with_kw(self, kw, sub_kw):
        return self.unchecked.with_kw(kw, sub_kw)
    
    def obj(self, name):
        self.unchecked.obj(name)
    
    def mor(self, name, source: Mor | Obj, target: Mor | Obj, value=None, proof=None) -> Mor | Unsourced | Eq:
        self.unchecked.mor(name, source, target, value, proof)
        theory = self.unchecked.theory
        _mor: Mor = getattr(theory, name)
        # Checking needs to occur after, since the actual mor might come
        # from kw.
        BObj = self.backend.Obj
        BMor = self.backend.Mor
        source = _mor.source
        target = _mor.target
        if isinstance(source, Obj):
            BObj.check(source)
        else:
            BMor.check(source)
        if isinstance(target, Obj):
            BObj.check(target)
        else:
            BMor.check(target)

    def eq(self, theory, name, ssource: Mor | Unsourced, starget: Mor | Unsourced, proof=None):
        self.unchecked.eq(name, ssource, starget, proof)
        theory = self.unchecked.theory
        _eq: Eq = getattr(theory, name)
        BMor = self.backend.Mor
        BMor.check(_eq.ssource)
        BMor.check(_eq.starget)
        scond = self.backend.Q.source_globular_cond
        tcond = self.backend.Q.target_globular_cond
        scond.verify(_eq)
        tcond.verify(_eq)

    def sub(self, name, theory_cls, **kw):
        self.unchecked.sub(name, theory_cls, **kw)

    class _Composer(Composer):
        @staticmethod
        def t_compose(c):
            return Category.t_compose(c)
        
        @staticmethod
        def compose_eq(c):
            return Category.compose_eq(c)
        
    class _Transer(Transer):
        @staticmethod
        def t_trans(p):
            return Category.t_trans(p)
        
    compose = variadic(Composer.compose)
    trans = variadic(Transer.trans)
    
# When checking e.g. Composable, it is often enough to just
# verify the equality, as applying the morphisms will check
# the source (so one does not need to check that the components
# are actually of type Mor).

# What about inductive type quiver?
# Allow it implicitly. Recursive function is defined as copair.
# This is especially required for monads.

# class N(wlex.Quiver):
#     Zero = _()
#     Succ = _('N')

# def Monad(C):
#     class D(wlex.Quiver): # or wlex.WLex?
#         T = _(C)
#         unit = _(_ >> T)
#         mul = _(T.T >> T)
#         left_unit = _(mul @ unit.T == T)
#         right_unit = _(mul @ T.unit == T)
#         assoc = _(mul @ mul.T == mul @ T.mul)
#     return D

# class C(wlex.Quiver):
#     M = own(Monad('C')) # so that M.T.T or _.T.T can be written instead of M.T.M.T

# spec Nat;
# type Zero;
# type Succ <- Nat;

# spec C;
# type T <- C;
# fn unit: C -> T;
# fn mul: T.T -> T;
# eq left_unit: mul @ unit.T == T;
# eq right_unit: mul @ T.unit == T;
# eq assoc: mul @ mul.T == mul @ T.mul;

# Monads and functors may be handled through special composition,
# e.g. by extending a string and by applying mul implicitly.
# The latter is an implicit type conversion. This is implicit
# at the language level but not at the theory level.
# f (x1, x2) when f is unary is an example of extending the string,
# namely the diagonal functor.

# Remaining questions re functors
# What's the use of natural transformations for inclusion functors.
# Nat trans must be monoidal when functors are monoidal. It seems.
# It seems the domain of an inclusion must be cartesian in order to
# allow functions f: X x Y -> Z, etc.
# Think of imports and interfaces.

# spec Program;
# type M <- Main with
#   main = print "Hello World!";

# face Main {
#   fn main: IO[()];
# }

# type Program: Main {
#   main = print "Hello World!";
# }

# type F: World -> World = (x: _, y: Y);

# All functors must be defined (they can be treated as macros).
# The builtin functors are the structure of World (including IO
# and the builtin data types). The problem with these functors
# (in contrast with the ones with limit domain) is that it's not
# automatically clear what the action on morphisms would be.

# Skip nat trans for inclusion functors!

# Interface as type of argument.

# face C {
#   type X :> World;
#   fn f: X -> String;
# }

# fn g: C$X -> String = C$f

# type Y: C {
#   X = String;
#   f = String;
# }

# g[Y] # = C$f[Y]

# Recall nat trans defs where X gets assigned a mor,
# and f an eq, etc.

# fn h: Y -> Z {
#   X = p;
#   f = e;
# }

# TODO: Canonical inclusion is a way to skip the `with` assignments.
# All canonical inclusions (even indirect through non canonical)
# coincide. The `with` assignments can only occur in the first
# inclusion. Handle canonical inclusion at the syntax level?
# Should inclusion of categories with ambient lex be canonical?

# Notice that assignment on the whole inclusion is not supported,
# except within the `with` block of an encompassing inclusion.

# There are no endoinclusions, and endofunctors such as monads arise
# from the structure of the category (even if axiomatically).
# What sub should handle is not lazy attribute access but avoiding
# self-reference by keeping a stack of classes.