from typing import override

from ..cells import *

# To avoid having to use generics in a complicated way,
# one has all the methods as abstract methods in the base,
# and trusts that the classes won't be mixed up (which the
# type checker is unable to guarantee). This is a compromise.

class CategoryObj(Obj):
    """Models object `category.Obj`"""
    @override
    def identity(self):
        return Comp(self)

class CategoryPrimObj(PrimObj, Obj):
    pass

class CategoryMor(Mor):
    @override
    def ref(self):
        return Ref(self)

    @override
    def compose(self, g: Mor):
        source = self.source
        f = self
        return Comp(source, f, g)

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
    def sym(self):
        return Sym(self)

    @override
    def trans(self, g: Eq):
        return Trans(self, g)

    @override
    def compose_eq(self, e: Eq):
        return CompEq(self, e)

class CategoryPrimEq(PrimEq, CategoryEq):
    # TODO: This type of multiple inheritance may not work with __slots__
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
    __slots__ = 'factors',
    factors: tuple[Mor, ...]

    def __init__(self, source: Obj, *factors: Mor):
        # TODO: It would make more sense to just flatten everything here
        # (and simplify the hint). In Trans this doesn't seem to be needed.
        # In fact this may support multiargs (just like Product and ProductMor).
        # TODO: Also just like Product and ProductMor disallow directly composing
        # with identity here, as the result would just be one of the args.
        # Cf. the case of single component Product/ProductMor with no name.
        # Id and Comp would become a single class.
        # Composing pairing with projection (or with pairing of projections)
        # results in single morphism (or pairing), so this should be handled
        # by Mor.compose.
        # DefMor is a wrapper around a Mor. It's the closest to parenthesization.
        # It may be better to simply replace (as is the case with Obj), in this case
        # one just needs to ability to set a name on any Mor (this helps with debugging).
        # This applies to ThesisEq.
        # Ideally one should make __eq__ ref and sym, however it may be possible
        # for it to not be trans nor compose_eq.
        # (f @ g) @ h == f @ (g @ h) == f @ k<g @ h> (k is DefMor)
        # The first == is ref((f @ g) @ h). The second == is ref(f) @ ref(g @ h).
        # See other notes about reg(g @ h) & ref(k) (__eq__ not being an equiv rel),
        # ref(f) @ ref(g) being the same as ref(f @ g), etc.
        # (f, g) @ h == (f @ h, g @ h) follows from PairingUnique, which is necessarily
        # intensional.
        if not factors:
            target = source
        else:
            target = factors[0].target
        super().__init__(source, target)

        _factors: list[Mor] = []
        for factor in factors:
            if isinstance(factor, Comp):
                _factors.extend(factor.factors)
            else:
                _factors.append(factor)

        if len(_factors) == 1:
            # Do identity stripping before instantiation.
            raise ValueError

        self.factors = tuple(_factors)
        # TODO: Because equal morphisms must have the same hash,
        # CartComp must accommodate p_eq.


    # TODO: Use always the most specific return type.
    def ev(self, x: object):
        # Why type checks here? The content of eval can only be dynamically
        # guaranteed to respect the signature. When skipping type checking
        # or making it static as much as possible one uses static.* or checked.*.
        # The backend uses part of static.* as its primitives. But not for type checking.
        # The fact that one doens't need any dynamic type checking within the functions of
        # static.* and checked.* (except for the args in checked.*). The result of dynamic
        # checking beyond the args is guaranteed by the assumption that one is replicating
        # the theory, which has a lex ambient, and there for can't be handled solely through
        # static type checking. The backend is the theory itself not its replication, only
        # the primitives need to be provided. The ambient of the backend can be static,
        # checked or dynamic. `compose` can only be defined in a lex ambient, because its
        # input requires a proof. Suspending all type checking when defining the theory is pointless
        # since defining the theory is compilation. The compiled ambient is checked since
        # dynamic type checking is still needed for the arguments. So the assumption that
        # a checked theory replicates the theory (hence no type checking beyond args of public interface) can
        # be restated as saying that the checked theory is the compiled theory.
        # Recall also that when the backend is being defined as a theory (no setting of primitives)
        # type checking is based on types not on elements. One can proof that the target of the primitive
        # is always the correct one (making check_target superfluous). More difficulty one can even prove
        # the same about the source. This would make all type checking superfluous.
        # Actually checked.* is not the compiled the theory, but the result of its execution after
        # setting primitives. This can code or functions produced at runtime,
        # e.g. for the public interface def compose(c): backend.Composable.check(c); backend.compose(c);
        # and the same pattern can be followed for the rest of the public interface.
        # Obviously backend is itself the private interface.
        # Obj.check is used in the public interface. What about Eq.proven?
        # Setting the primitives may actually be handled by using 2-(co)limits, or by using sub
        # (i.e. embedding the theory in a larger one). Relying on other theories still requires
        # setting primitives on those other theories.
        # Trusting the target of the eval primitive is analogous to not providing a proof when
        # assuming a primitive eq.
        # Variadic functions with conversions, etc. of course cannot be the result of compiling
        # the ambient theory, as this would be too complicated (although accomplishable with List, etc.),
        # so they are built on simple functions which take care of type checking the arguments.
        # What about the rest of the body of such complicated functions? Just assume the return type is correct.
        # The instantiation functions (obj, mor, eq) are also not part of the theory.

        res = x
        for factor in self.factors:
            res = factor.ev(res)
        return res

    def hint(self):
        return self.source, self.factors

    def same(self, x: Mor):
        # True should take less time.
        # True or False
        # Calling super().__eq__ would cause infinite loop.
        # TODO: This only applies to cart.Comp
        # TODO: In fact Mor of different classes should always be different.
        if self.eql_definitional(x):
            return True
        return (
            isinstance(x, Comp)
            and all(f.same(g) for f, g in zip(self.factors, x.factors))
            # This is required for comparing identities.
            and self.source.identical(x.source)
        )

    def __str__(self):
        return f'({'@'.join(str(factor) for factor in self.factors)})'

    def __repr__(self):
        return f'`comp {self!s}`'

class Sym(CategoryEq):
    inv: Eq

    def __init__(self, inv: Eq):
        self.inv = inv
        ssource = inv.starget
        starget = inv.ssource
        super().__init__(ssource, starget)

    @property
    def proven(self):
        return self.inv.proven

    def __str__(self):
        return f'~{self.inv}'

    def __repr__(self):
        return f'`sym {self!s}`'

class Trans(CategoryEq):
    __slots__ = 'factors',
    # There are two approaches (cf. CompEq). One is store the equalities
    # required for the proof, the other is to discard them.
    factors: tuple[Eq, ...]

    def __init__(self, ssource: Mor, *factors: Eq):
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
        if not factors:
            starget = ssource
        else:
            starget = factors[0].starget
        super().__init__(ssource, starget)

        _factors: list[Eq] = []
        for factor in factors:
            if isinstance(factor, Trans):
                _factors.extend(factor.factors)
            else:
                _factors.append(factor)

        if len(_factors) == 1:
            raise ValueError

        self.factors = tuple(_factors)

    @property
    def proven(self):
        return all(factor.proven for factor in self.factors)

    def __str__(self):
        return f'({'&'.join(str(factor) for factor in self.factors)})'

    def __repr__(self):
        return f'`trans {self!s}`'

class CompEq(CategoryEq):
    __slots__ = 'factors',
    factors: tuple[Eq, ...]

    def __init__(self, *factors: Eq):
        if len(factors) <= 1:
            # ref(id(source)) should be created using Comp
            raise ValueError
        source = factors[-1].ssource.source
        ssource = Comp(source, *(factor.ssource for factor in factors))
        starget = Comp(source, *(factor.starget for factor in factors))
        super().__init__(ssource, starget)
        self.factors = tuple(factors)

    @property
    def proven(self):
        return all(factor.proven for factor in self.factors)

    def __str__(self):
        return f'({'@'.join(str(factor) for factor in self.factors)})'

    def __repr__(self):
        return f'`comp_eq {self!s}`'