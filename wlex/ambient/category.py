from functools import wraps
from typing import Any
from collections.abc import Callable
import weakref

from .cells import (
    Obj, Mor, DefMor, HatMor, DefHatMor, Eq,
    Unsourced, PrimObj, PrimMor, PrimEq, ThesisEq,
)
from ..theory.category import Category as BCategory
    
class Error(Exception):
    pass

class Comp(Mor):
    __slots__ = 'f', 'g'
    f: Mor
    g: Mor

    def __init__(self, f: Mor, g: Mor):
        source = g.source
        target = f.target
        super().__init__(source, target)
        self.f = f
        self.g = g

    # TODO: Use always the most specific return type.
    def eval(
            self,
            x: object,
            check_source: bool = True,
            check_target: bool = True,
        ):
        # self is not Composable, so self.f is not a projection.
        return self.f.eval(
            self.g.eval(x, check_source=check_source),
            check_source=False,
            check_target=check_target,
        )
    
    def flat(self) -> tuple[Mor, ...]:
        if isinstance(self.f, (Comp, Id)):
            if isinstance(self.g, (Comp, Id)):
                return (*self.f.flat(), *self.g.flat())
            return (*self.f.flat(), self.g)
        elif isinstance(self.g, (Comp, Id)):
            return (self.f, *self.g.flat())
        else:
            return (self.f, self.g)
    
    def eql(self, x: Mor):
        # True should take less time.
        # True or False
        # Calling super().__eq__ would cause infinite loop.
        if self.eql_definitional(x):
            return True
        return _monoidal_eq(self, x)
            
    def __str__(self):
        return f'({self.f} @ {self.g})'
            
    def __repr__(self):
        return f'`comp {self!s}`'

class Id(Mor):
    __slots__ = ()

    def __init__(self, obj: Obj):
        super().__init__(obj, obj)
        # Recall that eval is only called by the checked ambient.
        #self.set_eval(lambda *args, **kwargs: (args, kwargs))

    def flat(self):
        return ()
    
    def eql(self, x: Mor):
        if self.eql_definitional(x):
            return True
        return (
            _monoidal_eq(self, x)
            and self.source == x.source
        )
    
    def eval(
            self, x: object, 
            check_source: bool = True,
            check_target: bool = True
        ):
        # TODO: Is it possible to have eval without type checking?
        # e.g. in the most concrete theory, which implements IO, etc.
        if check_source or check_target:
            self.source.check(x)
        return x
    
    def __str__(self):
        return f'{self.source}'
    
    def __repr__(self):
        return f'`id {self!s}`'

def _monoidal_eq(x: Comp | Id, y: Mor):
    return (
        isinstance(y, (Comp, Id))
        and all(vx.eql(vy) for vx, vy in zip(x.flat(), y.flat()))
    )

class UnsourcedComp(Unsourced):
    __slots__ = 'f', 'g', '_comp'
    # Eval is not supported until converting to Comp.
    # Conversion to Comp must occur even in the absence of
    # type checking.
    f: Mor
    g: Unsourced
    _comp: Callable[[Mor, Mor], Comp]

    def __init__(
            self, f: Mor,
            g: Unsourced,
            comp: Callable[[Mor, Mor], Comp],
        ):
        self.f = f
        self.g = g
        self._comp = comp

    def with_source(self, source: Obj):
        # source should always be checked to ba Mor
        # The full type checking for comp is done here.
        # To avoid failing so late, one may trying requiring f to be Mor and
        # precomposing it with g.target.identity. However, the target of g is
        # not actually determined until a source is set.
        return self._comp(
            self.f,
            self.g.with_source(source),
        )
    
    __str__ = Comp.__str__

    def __repr__(self):
        return f'`unsourced_comp {self!s}`'

class UnsourcedId(Unsourced):
    __slots__ = ()
    # TODO: Recall that pairing can be made out of unsourced components.
    def with_source(self, source: Obj):
        return source.identity()
    
    def __str__(self):
        return 'id'
    
    def __repr__(self):
        return '`unsourced_id`'
    
class Trans(Eq):
    __slots__ = 'f', 'g'
    f: Eq
    g: Eq

    def __init__(self, f: Eq, g: Eq):
        ssource = g.ssource
        starget = f.starget
        super().__init__(ssource, starget)
        self.f = f
        self.g = g
    
    @property
    def proven(self):
        return self.f.proven and self.g.proven
    
    def __str__(self):
        return f'({self.f} & {self.g})'
            
    def __repr__(self):
        return f'`trans {self!s}`'
    
class CompEq(Eq):
    __slots__ = 'd', 'e'
    d: Eq
    e: Eq

    def __init__(self, d: Eq, e: Eq):
        ssource  = d.ssource.compose(e.ssource)
        starget = d.starget.compose(e.starget)
        super().__init__(ssource, starget)
        self.d = d
        self.e = e

    @property
    def proven(self):
        return self.d.proven and self.e.proven
    
    def __str__(self):
        return f'{self.d} & {self.e}'
            
    def __repr__(self):
        return f'`comp_eq {self!s}`'

class Ref(Eq):
    __slots__ = ()

    def __init__(self, mor: Mor):
        super().__init__(mor, mor)
    
    @property
    def proven(self):
        return True

    def __str__(self):
        return f'{self.ssource}'
    
    def __repr__(self):
        # This appears to be ref(m) not ref[m].
        return f'`ref {self!s}`'
    
def _extract_subkw(kw: dict[str, object]):
    # Changes kw in place
    subkw: dict[str, dict[str, object]] = dict()
    key: str
    # Needs to get all the keys before calling pop
    for key in list(kw):
        skey = key.split('.', 1)
        if len(skey) > 1:
            d: dict[str, object] = dict()
            subkw[skey[0]] = d
            d[skey[1]] = kw.pop(key)
    return subkw

# class Path(NamedTuple):
#     f: Eq
#     g: Eq

# class Composable(NamedTuple):
#     f: Mor
#     g: Mor
Path = tuple[Eq, Eq]
Composable = tuple[Mor, Mor]
ComposableEq = tuple[Eq, Eq]
UniqueSource = tuple[Eq, Eq]
AssociativitySource = tuple[Mor, Mor, Mor]

# class ComposableEq(NamedTuple):
#     d: Eq
#     e: Eq

# class UniqueSource(NamedTuple):
#     d: Eq
#     e: Eq

# class AssociativitySource(NamedTuple):
#     f: Mor
#     g: Mor
#     h: Mor

def variadic(m: Callable[[Any, Any, Any], Any]):
    # This doesn't handle nullary.
    @wraps(m)
    def wrapper(self: Any, head: Any, *tail: Any):
        if not tail:
            return head
        return m(self, head, wrapper(*tail))
    return wrapper

#def unchecked_eval
# Python static type checking handles all type checking up until Cart.
# Actual checking is needed starting with backend Lex (as used by
# Composable in Category.t_compose). This means that one should preserve
# static type checking for the backend type checking, and make the latter
# only handle checking beyond Cart (Lex, etc.).
# One has to follow an all or nothing approach. It is too complicated
# to use the backend only for certain type checking while keeping the
# static type checking. One has a class PartiallyCheckedCategory,
# where checked means dynamically checked.
# Category, CheckedCategory, DynamicCategory.
# If Cart type checking end up being handled ad hoc, then so does the
# # remaining type checking. 

class Category:
    def __init__(
            self, theory: object, name: str = '',
            kw: dict[str, object] | None = None,
            subkw: dict[str, dict[str, object]] | None = None,
            theory_clss: tuple[type, ...] | None = None,
        ):
        # The point of this would be to allow type checking on the overriding
        # methods of CheckedCategory. This seems to not be needed.
        # see e.g. f.source, g.target. Here type checking would be
        # superfluous as one has already checked that (f, g) is Composable.
        #self.hat_mor_cls = HatMor.cls_with_id_comp(self.identity, self.t_compose)
        self.id = UnsourcedId()
        self.kw = kw or dict()
        self.subkw = subkw or dict()
        self.name = name
        self.theory_clss = theory_clss or ()
        self.theory: object = weakref.proxy(theory)

    @classmethod
    def with_kw(
            cls, theory: object, name: str,
            kw: dict[str, object],
            subkw: dict[str, dict[str, object]],
            theory_clss: tuple[type, ...],
        ):
        # This needs to handle kw used by sub at lower levels.
        # e.g. S.P.Q in line 35 of theory/category.py.
        # TODO: An important goal is to be able to define monads,
        # hence natural transformations. This requires making mor
        # support self and self.T within the __init__ of the theory
        # as if they were functors.
        # Inheritance requires this to be a classmethod.

        return cls(theory, name, kw, subkw, theory_clss)

    def obj(self, name: str):
        theory = self.theory
        if name in self.kw:
            setattr(theory, name, self.kw[name])
        else:
            setattr(theory, name, PrimObj(self.cell_name(name)))

    def mor(
            self, name: str,
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
        #print(self, source, target, value, proof)
        if name in self.kw:
            if value or proof:
                raise Error
            # The purpose of setting the value indirectly is to check signature.
            _value = self.kw[name]
            if isinstance(_value, Mor | Unsourced | Obj):
                value = _value
            else:
                raise TypeError

        #print(value, self.kw)
        if isinstance(source, Obj) and isinstance(target, Obj):
            if proof:
                raise Error
            if value:
                setattr(theory, name, DefMor(
                    self.cell_name(name),
                    source, target, value,
                ))
            else:
                setattr(theory, name, PrimMor(
                    self.cell_name(name),
                    source, target,
                ))
        elif value:
            #print(value)
            if not proof:
                if isinstance(value, Mor):
                    proof = value.hat
            if proof:
                setattr(theory, name, DefHatMor(
                    self.cell_name(name),
                    source, target, value, proof,
                ))
        else:
            # HatMor.unfold_source_target handles the remaining type checking.
            setattr(theory, name, HatMor(
                self.cell_name(name),
                source, target,
            ))

    def eq(
            self, name: str,
            ssource: Mor | Unsourced | Obj,
            starget: Mor | Unsourced | Obj,
            proof: Eq | Mor | Obj | None = None,
        ):
        theory = self.theory
        if name in self.kw:
            if proof:
                raise Error
            _proof = self.kw[name]
            if isinstance(_proof, Eq | Mor | Obj):
                proof = _proof
            else:
                raise TypeError

        ssource, starget = (
            m.identity() if isinstance(m, Obj) else m
            for m in (ssource, starget)
        )
        
        if isinstance(ssource, Unsourced):
            if isinstance(starget, Unsourced):
                raise Error
            #if not isinstance(starget, Mor):
            #    raise TypeError
            ssource = ssource.with_source(starget.source)
        elif isinstance(starget, Unsourced):
            #if not isinstance(ssource, Mor):
            #    raise TypeError
            starget = starget.with_source(ssource.source)
        #elif not (isinstance(ssource, Mor) and isinstance(starget, Mor)):
        #    raise TypeError

        if isinstance(proof, Obj):
            proof = proof.identity()
        if isinstance(proof, Mor):
            proof = proof.ref()
        
        # Eq.__eq__ in Eq.__init__ checks that proof is of type Eq or None.
        if proof:
            setattr(
                theory, name,
                ThesisEq(
                    self.cell_name(name),
                    ssource, starget,
                    proof
                )
            )
        else:
            setattr(
                theory, name,
                PrimEq(
                    self.cell_name(name),
                    ssource, starget,
                ),
            )

    def sub(self, name: str, theory_cls: type, **kw: object):
        # If both self.subkw and kw override cells then an error
        # occurs, because what should have happened is that the overriding
        # cell got overridden. This applies to subkw as well.
        # kw gets separated into kw and subkw.
        # subkw is a dict with kw values used for the sub's
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
            if self.subkw.get(name):
                # Can't be overriden by subkw when overridden by kw.
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

        if name in self.subkw:
            superkw: dict[str, object] = self.subkw[name]
            for key, value in superkw.items():
                if key in kw:
                    raise Error
                kw[key] = value

        # TODO: Place this in __init__?
        subkw = _extract_subkw(kw)
        #setattr(theory, name, Sub(name, self, theory_cls, kw, subkw))
        # Avoid circular class instantiation
        theory_clss: tuple[type, ...] = (*self.theory_clss, type(theory))
        for tc in theory_clss:
            if theory_cls is tc:
                raise Error
        subname = self.cell_name(name)
        setattr(
            theory, name,
            # TODO: Why not use Category instead of self.with_kw?
            # TODO: Check if this should be simplified further since
            # subs can be created without lazy instantiation. Probably not. 
            theory_cls(lambda th: self.with_kw(th, subname, kw, subkw, theory_clss)),
        )

    def cell_name(self, name: str):
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
        f, g = c
        return f.compose(g)
        
    @staticmethod
    def identity(obj: Obj) -> Mor:
        return obj.identity()
    
    @staticmethod
    def ssource(eq: Eq) -> Mor:
        return eq.ssource
    
    @staticmethod
    def starget(eq: Eq) -> Mor:
        return eq.starget
    
    @staticmethod
    def ref(mor: Mor) -> Eq:
        return mor.ref()
    
    @staticmethod
    def t_trans(p: Path) -> Eq:
        f, g = p
        return f.trans(g)

    @staticmethod
    def eq_unique(s: UniqueSource) -> Eq:
        d, _ = s
        return d
    
    @staticmethod
    def sym(eq: Eq) -> Eq:
        return eq
    
    @staticmethod
    def associativity(s: AssociativitySource) -> Eq:
        f, g, h = s
        # Type checking s and return value is enough.
        return f.compose(g).compose(h).ref()
    
    @staticmethod
    def compose_eq(c: ComposableEq) -> Eq:
        d, e = c
        return d.compose_eq(e)
        
    def _compose(
        self,
        f: Mor | Unsourced | Eq | Obj,
        g: Mor | Unsourced | Eq | Obj,
    ) -> Mor | Unsourced | Eq:
        # No further type checking is or should be needed here.
        # Being Composable is the only requirement available for
        # type checking at the lang level. Being Composable means
        # having f, g of type Mor with the equality of source and target
        # (as checked by the Lex backend).
        # This should work like syntax sugar with respect to e.g.
        # composing a Mor and an Obj, etc. Hence calls like
        # ref, ssource, target identity, etc. should all support
        # backend type checking. The would support backend type checking
        # if t_compose, t_compose_eq where manually used.
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

        def comp(u: Mor, v: Mor):
            u = u.weaken(v.target)
            return self.t_compose((u, v))
        
        def comp_eq(u: Eq, v: Eq):
            u = u.weaken(v.ssource.target)
            # This will type check g to be Eq.
            return self.compose_eq((u, v))

        f, g = (
            m.identity() if isinstance(m, Obj) else m
            for m in (f, g)
        )

        # Unsourced, Eq comp is allowed but not Eq, Unsourced. 
        if isinstance(g, Unsourced):
            if isinstance(f, Eq):
                # For consistency, there is no UnsourcedCompEq.
                # We'd have to compose with the ref of Unsourced,
                # which is an equality of Unsourced and therefore
                # not allowed.
                raise Error
            
            # amb.t_compose backend type checking would ensure that
            # f is Mor. We check that here for consistency with the
            # next block and to fail earlier.
            if not isinstance(f, Mor):
                raise TypeError
            return UnsourcedComp(f, g, comp)

        if isinstance(f, Unsourced):
            if isinstance(g, Eq):
                # No checking needed with ref
                s = g.ssource.target
                f = f.with_source(s).ref()
                return self.compose_eq((f, g))
            if not isinstance(g, Mor):
                raise TypeError
            f = f.with_source(g.target)
            return self.t_compose((f, g))

        if isinstance(f, Eq):
            if isinstance(g, Mor):
                g = g.ref()
            return comp_eq(f, g)
        
        if isinstance(g, Eq):
            f = f.ref()
            return comp_eq(f, g)
        
        return comp(f, g)

    def _trans(self, f: Eq | Mor | Obj, g: Eq | Mor | Obj) -> Eq:
        # Handle identity
        f, g = (
            m.identity().ref() if isinstance(m, Obj) else
            (m.ref() if isinstance(m, Mor) else m)
            for m in (f, g)
        )
        return self.t_trans((f, g))
        
    compose = variadic(_compose)
    trans = variadic(_trans)

class CheckedCategory:
    # TODO: Type annotate as Callable?
    unchecked_cls = Category
    backend: BCategory
    unchecked: Category

    @staticmethod
    def check_obj(x: object) -> bool:
        return isinstance(x, Obj)
    
    @staticmethod
    def check_mor(x: object) -> bool:
        return isinstance(x, Mor)
    
    @staticmethod
    def check_eq(x: object) -> bool:
        return isinstance(x, Eq)

    def __init__(
            self, theory: object,
            backend: BCategory, 
            kw: dict[str, object] | None = None,
            subkw: dict[str, dict[str, object]] | None = None,
            theory_clss: tuple[type, ...] | None = None,
        ):
        # Notice that type checking only needs to be done the first
        # time theory_cls is instantiated when there is no sub overriding.
        self.unchecked = self.unchecked_cls(
            theory,
            kw=kw, subkw=subkw,
            theory_clss=theory_clss,
        )
        self.backend = backend
        self.id = self.unchecked.id
        self.weakened = self.unchecked.weakened

    def set_semantics(self, backend: BCategory):
        u = self.unchecked
        # The backend provides only structure, no semantics.
        # backend Category is based on ambient Lex.
        # This means some of the set_check, set_eval and assume
        # is already implemented, e.g. Composable, eq, etc.
        # It makes sense then to disallow set_check, set_eval and
        # assume from the non atomic cells.
        #Obj().set_check(u.check_obj)
        Mor(Obj(), Obj()).set_eval(
            u.source # type: ignore
        )
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

    def with_kw(self, theory, name, kw, subkw, theory_clss):
        return CheckedCategory(theory, self.backend, name, kw, subkw, theory_clss)

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
        
    #def with_kw(self, kw, subkw):
    #    return self.unchecked.with_kw(kw, subkw)
    
    def obj(self, name):
        self.unchecked.obj(name)
    
    def mor(
            self, name,
            source: Mor | Obj,
            target: Mor | Obj,
            value: Mor | Unsourced | Obj | None = None,
            proof: Eq | Mor | Obj | None = None
        ):
        self.unchecked.mor(name, source, target, value, proof)
        theory = self.unchecked.theory
        _mor: Mor = getattr(theory, name)
        # Checking needs to occur after, since the actual mor might come
        # from kw.
        BObj = self.backend.Obj
        BMor = self.backend.Mor
        source = _mor.source
        target = _mor.target
        # Redundant but consistent. This checks the signatures of source and target.
        BMor.check(_mor)
        BObj.check(source)
        BObj.check(target)            

    def eq(
            self, name,
            ssource: Mor | Unsourced | Obj,
            starget: Mor | Unsourced | Obj,
            proof: Eq | Mor | Obj | None = None,
        ):
        self.unchecked.eq(name, ssource, starget, proof)
        theory = self.unchecked.theory
        _eq: Eq = getattr(theory, name)
        BMor = self.backend.Mor
        BEq = self.backend.Eq
        BEq.check(_eq)
        BMor.check(_eq.ssource)
        BMor.check(_eq.starget)
        scond = self.backend.Q.source_globular_cond
        tcond = self.backend.Q.target_globular_cond
        scond.verify(_eq)
        tcond.verify(_eq)

    def sub(self, name, theory_cls, **kw):
        # TODO: Does this work?!!
        self.unchecked.sub(name, theory_cls, **kw)

    compose = variadic(Category._compose)
    trans = variadic(Category._trans)
    
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