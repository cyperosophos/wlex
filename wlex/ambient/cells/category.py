from typing import override

from ..cells import *

# To avoid having to use generics in a complicated way,
# one has all the methods as abstract methods in the base,
# and trusts that the classes won't be mixed up (which the
# type checker is unable to guarantee). This is a compromise.

class CategoryObj(Obj):
    @override
    def identity(self):
        return Id(self)

class CategoryPrimObj(PrimObj, Obj):
    pass

class CategoryMor(Mor):
    @override
    def ref(self):
        return Ref(self)
    
    @override
    def compose(self, g: Mor):
        f = self
        return Comp(f, g)
    
    # TODO: This goes is cart.Mor
    # def eql(self, x: cells.Mor):
    #     from ..category import Comp
    #     if super().eql(x):
    #         return True
    #     if isinstance(x, Comp):
    #         # Defer to Comp.__eq__.
    #         # This is especially useful in the case of p_eq, q_eq of pairing.
    #         return x.eql(self)
    #     return False
    
class CategoryPrimMor(PrimMor, CategoryMor):
    pass

class CategoryDefMor(DefMor, CategoryMor):
    pass

class CategoryEq(Eq):
    @override
    def trans(self, g: Eq):
        return Trans(self, g)
    
    @override
    def compose_eq(self, e: Eq):
        return CompEq(self, e)
    
class CategoryPrimEq(PrimEq, CategoryEq):
    pass

class CategoryThesisEq(ThesisEq, CategoryEq):
    pass

class CategoryHatEq(HatEq, CategoryEq):
    pass

class CategoryHatMor(HatMor, CategoryMor):
    hat_eq_cls = CategoryHatEq

class CategoryDefHatMor(DefHatMor, CategoryMor):
    hat_eq_cls = CategoryHatEq

class Comp(CategoryMor):
    __slots__ = 'f', 'g'
    f: Mor
    g: Mor

    def __init__(self, f: Mor, g: Mor):
        # TODO: It would make more sense to just flatten everything here
        # (and simplify the hint). In Trans this doesn't seem to be needed.
        # In fact this may support multiargs (just like Product and ProductMor).
        # TODO: Also just like Product and ProductMor disallow directly composing
        # with identity here, as the result would just be one of the args.
        # Cf. the case of single component Product/ProductMor with no name.
        # Id and Comp would become a single class.
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
    
    def hint(self) -> tuple[Mor, ...]:
        # TODO: Because equal morphisms must have the same hash,
        # CartComp must accommodate p_eq.
        if isinstance(self.f, (Comp, Id)):
            if isinstance(self.g, (Comp, Id)):
                return *self.f.hint(), *self.g.hint()
            return *self.f.hint(), self.g
        elif isinstance(self.g, (Comp, Id)):
            return self.f, *self.g.hint()
        else:
            return self.f, self.g
    
    def eql(self, x: Mor):
        # True should take less time.
        # True or False
        # Calling super().__eq__ would cause infinite loop.
        # TODO: This only applies to cart.Comp
        if self.eql_definitional(x):
            return True
        return _monoidal_eq(self, x)
            
    def __str__(self):
        return f'({self.f} @ {self.g})'
            
    def __repr__(self):
        return f'`comp {self!s}`'

class Id(CategoryMor):
    __slots__ = ()

    def __init__(self, obj: Obj):
        super().__init__(obj, obj)
        # Recall that eval is only called by the checked ambient.
        #self.set_eval(lambda *args, **kwargs: (args, kwargs))

    def hint(self):
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
        and all(vx.eql(vy) for vx, vy in zip(x.hint(), y.hint()))
    )

class Trans(CategoryEq):
    __slots__ = 'f', 'g'
    f: Eq
    g: Eq

    def __init__(self, f: Eq, g: Eq):
        # If one treats sym as id, then one would have to check
        # the direction of f and g, this amounts to dyn typ checking,
        # which is handled in checked.category.trans. However, the
        # code here should work even without type checking.
        # TODO: The biggest problem with treating sym as id is in
        # compose_eq. There is no way to determine if one gets
        # f(x) = g(y) or f(y) = g(x). Suppose one would like to
        # apply trans with g(x) = k. There is no way to know if one
        # must also apply trans with g(x = y).
        # The solution is to treat sym the way type conversions
        # (renaming, weakening) are treated. One has to handle it
        # in high level trans and in Category.eq (for checking
        # signature of proof when producing ThesisEq).
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
    
class CompEq(CategoryEq):
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

class Ref(CategoryEq):
    __slots__ = ()

    def __init__(self, mor: Mor):
        super().__init__(mor, mor)

    def __str__(self):
        return f'{self.ssource}'
    
    def __repr__(self):
        # This appears to be ref(m) not ref[m].
        return f'`ref {self!s}`'
    
    @property
    def proven(self):
        return True