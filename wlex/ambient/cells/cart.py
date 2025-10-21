from typing import Union, TypeVar, TypeGuard, override, overload
from collections.abc import Sequence, MutableSequence, Mapping, Sized

from .category import *

ProductParam = tuple[str, 'Obj'] | tuple[tuple[str, ...], 'Product']
ProductParamName = Union[str, 'Obj']
ProductParamKey = int | ProductParamName
ProductMorParam = tuple[str | tuple[str, ...], 'Mor']
ProductProjParam = tuple[str | tuple[str, ...], ProductParamKey]
# TODO: Include all Cart cells here, e.g. Product, ProductMor

class CartObj(CategoryObj):
    # TODO: Keep high-level interface in the ambient class (Cart).
    # It seems that having a proj method in Product makes sense,
    # since they proj corresponds to the legs of the span returned
    # by the theoretical product morphism,
    # however it's not clear that a multiarg proj is sufficiently
    # low level to be had here. One can have the high-level pairing
    # itself accept keys as arguments instead of only morphisms.
    # Having compose also accept keys is probably overkill and
    # too complicated since one would then have to distinguish
    # coprojections and param projections. Param projections are
    # the way one handles vars within the body of a morphism (check
    # prev notes). The idea should be simple. There are access ops
    # (i.e. projections) and assignments. Assignments expand the
    # product element, and access ops are the usual projections.
    # Assignments are pairings with the identity.
    # Nothing changes about the composition. It seems there is a benefit to
    # supporting parallel assignments. Whereas naturality doesn't translate
    # to parallelism but simply to the choice two equal compositions,
    # parallel assignment can be interpreted as such in the appropriate
    # computational environment. This isn't simply a matter of optimization,
    # but of explicitly representing the program.
    # Parallel assignment are invisible to each other. This is useful.
    # def proj2(
    #         self, *args: ProductParamKey | ProductProjParam,
    #         **kwargs: ProductParamKey,
    #     ):
    #     from ..cart import ProductMor
    #     if not (args or kwargs):
    #         return ProductMor(self, ())
        
    #     if len(args) > 0:
    #         if len(args) > 1 or kwargs:
    #             raise ValueError
    #         arg = args[0]
    #         if isinstance(arg, tuple):
    #             name, key = arg
    #         else:
    #             name = ''
    #             key = arg
    #     elif len(kwargs) > 1:
    #         raise ValueError
    #     else:
    #         # Notice that the type checker is permissive here.
    #         name, key = list(kwargs.items())[0]

    #     if key == self:
    #         mor = self.identity()
    #         if name:
    #             return ProductMor(self, ((name, mor),))
    #         return mor
    #     raise ValueError
    
    @override
    def proj(self, key: ProductParamKey) -> Mor:
        if key == self:
            return self.identity()
        raise ValueError
    
    @override
    @staticmethod
    def terminal():
        return Product(())
    
    @override
    def terminal_mor(self):
        # The result of this has to pass backend.TerminalMor.check.
        #return Mor(self, Product(()))
        return ProductMor(self, ())
        # See cart.weaken_mor
    
    @override
    def product(self, y: Obj):
        # This result of this has to pass backend.Span.check.
        # We use Product for purity (since it defines __eq__),
        # but we don't need its check method. When definining the
        # backend theory, the morphisms returned here are not used
        # as projections, so there is no need for eval (although
        # one still should have purity and composition).
        x = self
        source = Product((('x', x), ('y', y)))
        #return Mor(source, x), Mor(source, y)
        # Use proj for purity
        return source.proj('x'), source.proj('y')

class CartPrimObj(CategoryPrimObj, CartObj):
    pass

class CartMor(CategoryMor):
    # TODO: This has to be just Ref, cf. Associativity, left_identity, etc.
    # def terminal_mor_unique(self):
    #     # Just like with comp, we don't check the equalizer.
    #     from ..ambient.cart import TerminalMorUnique
    #     return TerminalMorUnique(self)
    @override
    def pairing(self, q: 'Mor'):
        p = self
        # There is no need to check this construction in checked/cart.py,
        # since it is not taking by any function as argument.
        # The produced instance is not used for type checking
        # (nor evaluating, nor proving). For type checking, one
        # uses Pairing (which supports multiple components).
        # Instances of both TerminalMor and ProductMor must pass
        # type checking by Pairing (and the hat).
        # Here the names end up being discarded.
        pm = ProductMor(p.source, (('p', p), ('q', q)))
        return pm, p, q, Ref(p), Ref(q)
    
def _isinstance_sequence_object(x: object) -> TypeGuard[Sequence[object]]:
    return isinstance(x, Sequence)

def _isinstance_mutable_sequence_object(x: object) -> TypeGuard[MutableSequence[object]]:
    return isinstance(x, MutableSequence)

# TODO Use @overload where needed instead of unions. 
class Product(CartObj, Sequence[Obj]):
    # TODO: Consider implementing W-Cart. W-Types don't require all limits.
    # In this case one would have two possible backends for Category:
    # one based on ambient Lex, and another based on ambient Dist (extensive cartesian).
    # In the latter `compose` relies on the Maybe monad.
    # See: nlab/ Polynomial functor (literal polynomial functor)
    # See: nlab/ Polynomail monad (free monoid)
    # See: nlab/ Extensive category
    # See: nlab/ Distributive categories
    __slots__ = 'components', 'names'
    _terminal: 'Product'
    components: dict[ProductParamName, tuple[int, Obj]]
    names: list[ProductParamName]

    def proj(self, key: ProductParamKey):
        if isinstance(key, int):
            name = self.pos_to_name(key)
        else:
            name = key
        return Proj(name, self)

    def __new__(cls, params: Sequence[ProductParam]):
        if not params:
            if not hasattr(cls, '_terminal'):
                cls._terminal = super().__new__(cls)
            return cls._terminal
        return super().__new__(cls)

    def __getitem__(self, idx: int): # type: ignore
        return self.pos_to_type(idx)

    # TODO: Check where is this being used!
    #def __contains__(self, key: object):
    #    if isinstance(key, int):
    #        return 0 <= key < len(self)
    #    return key in self.components
    
    def includes(self, prod: 'Product') -> bool:
        return all(
            name in self.components
            and self.name_to_type(name) == prod.name_to_type(name)
            for name in prod.names
        )

    def name_to_type(self, name: ProductParamName):
        return self.components[name][1]

    def _add_name(self, name: ProductParamName, typ: Obj):
        if name in self.components:
            _, t = self.components[name]
            if not t.equiv(typ):
                raise ValueError
        else:
            self.components[name] = (len(self.components), typ)

    def pos_to_type(self, pos: int):
        return self.components[self.names[pos]][1]
    
    def pos_to_name(self, pos: int):
        return self.names[pos]

    def pos_to_name_and_type(self, pos: int):
        name = self.names[pos]
        return name, self.components[name][1]

    def __init__(self, params: Sequence[ProductParam]):
        if not params and self is self._terminal and hasattr(self, 'params'):
            return
        
        self.components = dict() # maps to position

        if len(params) == 1:
            # Disallow Product as single component
            # and nameless single component.
            name, typ = params[0]
            if isinstance(typ, Product):
                raise ValueError
            elif not name:
                raise ValueError

        for arg in params:
            name, typ = arg
            # Shallow overriding of names
            if isinstance(name, tuple):
                if not isinstance(typ, Product):
                    raise TypeError
                if len(name) != len(typ):
                    raise ValueError
                for i, subname in enumerate(name):
                    # Repeated subname is allowed.
                    if subname:
                        self._add_name(subname, typ.pos_to_type(i))
                    else:
                        # An empty subname will keep the original subname.
                        # This means that, in the case of a named product subparam,
                        # no further flattening will occured, it will remain as a Product param.
                        self._add_name(*typ.pos_to_name_and_type(i))
            elif name: # name is str
                self._add_name(name, typ)
            elif isinstance(typ, Product):
                for subname, (_, t) in typ.components.items():
                    self._add_name(subname, t)
            else:
                # The type is the name
                self._add_name(typ, typ)
            # TODO: This assumes other limits will be subclasses
            # of Product. But this doesn't make a lot of sense in
            # the case of an equalizer. The solution seems to treat
            # subsets (equalizers) of Product as Product.
            # Recall however that the equality of the equalizer requires
            # using a name for the single parameter.
            # Also one may use a single parameter product in order to
            # set the name of a parameter before a nameless product parameter.
            # Hence treat equalizers (when needed) as single parameter products.
        self.names = list(self.components.keys())

    def equiv(self, x: Obj):
        # TODO: Notice that the order matters when comparing to Product
        # types, however the order does not matter when checking an object
        # of type Mapping. When a morphisms (e.g. a pairing) is guarantied
        # to always produce Mapping, the return type should reflect this,
        # i.e. it should be a product type that only accepts Mappings (probably not needed).
        # What is in fact needed is type conversions (similar to weakening)
        # between Product types with the same list of names but distinct orderings.
        # They are not equiv but isomorphic. The situation here should be handled
        # just like weakening. One can also have conversions when the types
        # coincide (and have the same order) but the names are different.
        # This is useful with pairig where the names aren't specified and
        # are therefore indices.
        return super().equiv(x) or (
            isinstance(x, Product)
            and all(
                n == m and s.equiv(t)
                for (n, (_, s)), (m, (_, t))
                in zip(self.components.items(), x.components.items())
            )
        )
    
    def hint(self):
        return ((n, s) for n, (_, s) in self.components.items())
    
    def __len__(self):
        return len(self.components)
    
    # def _check(self, x: Sequence[object]):
    #     # Handle the mandatory flattening of nameless parameters in x that provide
    #     # subparameters. This is done with args and kwargs whose keys
    #     # are tuples.
    #     # TODO: Fix the following in the sample syntax (wlex files) and theory code where needed?
    #     # One cannot directly determine the position of a parameter due to flattening.
    #     # Hence nameless parameters must be product types (i.e. provide suparameters).
    #     # Repeating the product type without names has no effect, i.e. it is the same as
    #     # including the product type only once.
    #     # If the overriding name is a tuple, names must be provided for all subparams.
    #     # TODO: If it is a dict (or k, v list), then only overridden names.
    #     for name, (_, typ) in self.components.items():
    #         typ.check(self._get_from_sequence(x, name))

    def _get_from_sequence(self, x: Sequence[object], name: ProductParamName):
        # No requirements are made here about x passing the type check.
        # We don't allow index instead of name, because flattening makes indices too complicated.
        return x[self.components[name][0]]

    def proj_raw_eval(self, x: object, name: ProductParamName):
        # No need to check length, since this would be part of actual eval method in Proj.
        # Being Mapping | Sequence is guarantied by the type checking of Proj.eval since its
        # parameter is of type Product(...).

        #if isinstance(x, Mapping):
        #    return self._get_from_mapping(x, name)
        #return self._get_from_sequence(x, name)
        # Type checking here is more forgiving.
        if _isinstance_sequence_object(x):
            return self._get_from_sequence(x, name)
        return x
    
    def check(self, x: object):
        # x can be category.AttrDict, tuple or dict.
        # AttrDict is simply treated as dict.
        # There can be an optional name of the parameter,
        # if this name is a tuple then it is treated as a list
        # of names for the parameters within the parameter.
        # If no name is provided for a parameter which is made out
        # of parameters, then the names of the parameters within the
        # parameter (suparameters) can be used. The subparameter from
        # a nameless subparameter are treated as parameters.
        # The result is that some parameters may end up having the same
        # name, this useful with subparameters. One has to check that
        # their values are equal (no need to be identical?).
        # This simply corresponds to the fact that AxBxC is the pullback
        # of the projections AxB->B and BxC->B.
        # One does not explicitly use this construction, since one is
        # not requiring equalities (as in equalizers). Also, the checked
        # values do not have repeated names. This makes it superfluous
        # to check equality, subparameters being identical follows automatically.

        # TODO: Reconsider basing the check on weakening (same applies to check_eql).
        # It may be better to keep the conversion explicit (only implicit at the syntax level),
        # especially since conversions are always needed (for backend eval and for concrete composition,
        # i.e. calling methods in checked and static).
        # Having check pass on types, for which conversion is required anyways,
        # is redundant.

        if isinstance(x, Sized):
            length = len(x)
        else:
            length = 1

        if length != len(self.components):
            raise Error
        
        if _isinstance_sequence_object(x):
            for name, (_, typ) in self.components.items():
                typ.check(self._get_from_sequence(x, name))
        elif self.components:
            # TODO: Projection must handle an argument like x (not a collection).
            # TODO: What if there is only one param, and it is itself a product?
            #       Disallow this kind of product!!?
            self.pos_to_type(0).check(x)
        else:
            raise Error
    
    # @staticmethod
    # def _sequence_from_subnames[T: ProductElement](
    #     x: T,
    #     subnames: tuple[str, ...],
    #     typ: 'Product',
    #     _get: ProductGetter[T],
    # ):
    #     return [
    #         _get(x, subname or typ.pos_to_name(i))
    #         for i, subname in enumerate(subnames)
    #     ]
    
    # @staticmethod
    # def _sequence_from_type[T: ProductElement](
    #         x: T,
    #         typ: 'Product',
    #         _get: ProductGetter[T],
    #     ):
    #     return [
    #         _get(x, subname)
    #         for subname in typ.names
    #     ]
        
    def check_eql(self, x: object, y: object):
        # This assumes that the type of x, y has already been checked.
        #if isinstance(x, Mapping):
        #    x = x.items()
        #if isinstance(y, Mapping):
        #    y = y.items()
        # TODO: This has to handle weakened, so iterating over x, y is useless.
        # Since type checking is done elsewhere. This should always work as if weakened were True.
        #return all(
        #    typ.check_eq(u, v) for u, v in zip(x, y)
        #)
        # Under weakened checking x and y can be equal even if they don't have the
        # same number of components.
        _x, _y = (
            v if _isinstance_sequence_object(v) else (v,)
            for v in (x, y)
        )
        _gfs = self._get_from_sequence
        for name, (_, typ) in self.components.items():
            typ.check_eql(_gfs(_x, name), _gfs(_y, name))

    def __str__(self):
        return f'({', '.join(f'{name}: {typ}' for name, (_, typ) in self.components.items())})'
    
    def __repr__(self):
        return f'`product {self!s}`'
    
class Proj(CartMor):
    def __init__(self, name: ProductParamName, source: Obj):
        self.name = name
        target = self._get_target(source)
        super().__init__(source, target)

    def _get_target(self, source: Obj):
        if isinstance(source, Product):
            # Get the type corresponding to self.key.
            return source.name_to_type(self.name)
        elif source is self.name:
            # source must be self.key. Return it unchanged.
            # source and self.key are required to be identical.
            # This seems to work because it doesn't make sense for
            # key to be a Product. If one needs to extract multiple attributes,
            # one uses a pairing of projections.
            return source
        else:
            raise ValueError
    
    def eval(
        self, x: object,
        check_source: bool = True,
        check_target: bool = True,
    ):
        source = self.source
        if isinstance(source, Product):
            if check_source:
                source.check(x)
            y = source.proj_raw_eval(x, self.name) # Must occur after check_source
            if check_target and not check_source:
                # If source has been checked, there is no need to check the target.
                target = self.target
                target.check(y)
            return y
        else:
            # Same as category.Id
            if check_source or check_target:
                source.check(x)
            return x
        
    def eql(self, x: Mor):
        if super().eql(x):
            return True
        return (
            isinstance(x, Proj)
            and self.name == x.name
            and self.source.equiv(x.source)
        )
    
    def hint(self):
        return self.name, self.source

    def __str__(self):
        name = self.name
        if isinstance(name, str):
            return f'{name}$'
        return str(name)

    def __repr__(self):
        return f'`proj {self!s}[{self.source}]`'
    
class ProductMor(CartMor):
    # There should also be UnsourcedProductMor which can only be the result
    # of having a pairing (ProductMor) consisting only of unsourced morphisms.
    # When not all morpshisms are unsourced, one must use these to determine
    # the source of the unsourced morphisms.
    __slots__ = 'components',
    # The names are in the target.
    # The bool is unpack flag.
    components: list[tuple[bool, Mor]]
    #names: list[ProductParamName]

    @staticmethod
    def _add_name(
        components: dict[ProductParamName, Mor],
        mor_to_eq: dict[Mor, Eq],
        name: ProductParamName,
        mor: Mor,
    ):
        if name in components:
            m = components[name]
            if mor in mor_to_eq:
                e = mor_to_eq[mor]
            else:
                raise ValueError
            if not e.parallel(Eq(m, mor)):
                raise ValueError
            return False
        components[name] = mor
        return True

    def __init__(
        self, source: Obj, params: Sequence[ProductMorParam],
        consistency: Sequence[Eq] = (),
    ):
        # In the high level interface, one uses continuation to pass the glue? No.
        # One simply passes the proofs in the args, and identifies them based on their
        # ssource and starget (the morphisms which must be equal).
        # This turns out mos useful when there is overlaps between return values
        # of product type. In this case, composing with proj is needed.

        # This must mostly work the same as Product.__init__ except for
        # repeated keys. In the case of repeated keys one needs proof
        # that their corresponding values will always be the same.
        
        # TODO: when doing assignments there is a pairing with the identity on the
        # product. A reassignment thus would require glue to prove that the assigned
        # value is the same as the one already assigned. Truly reassigning would require
        # removing the old value through projection pairing.
        #self.components = dict()

        if len(params) == 1:
            name, mor = params[0]
            typ = mor.target
            if isinstance(typ, Product):
                raise ValueError
            elif not name:
                raise ValueError
        
        self.components = []
        components = self.components
        target_params: list[ProductParam] = []
        # The Mor here is the Mor composed with the projection so its target
        # is the object corresponding to the name.
        name_to_mor: dict[ProductParamName, Mor] = dict()
        # Recall that overlap goes no deeper that the first level of names.
        # However, it is still difficult to rely on this as mapping key due to DefMor,
        # etc. One solution is to define __hash__ as a hint.
        mor_to_eq: dict[Mor, Eq] = dict()
        # No renaming here, only composition with projections.
        for e in consistency:
            et = e.starget
            if et in mor_to_eq:
                raise ValueError
            mor_to_eq[et] = e

        for arg in params:
            name, mor = arg
            typ = mor.target
            if not mor.source.equiv(source):
                raise ValueError
            if isinstance(name, tuple):
                if not isinstance(typ, Product):
                    raise TypeError
                target_params.append((name, typ))
                if len(name) != len(typ):
                    raise ValueError
                # Make a renaming pairing to compose with mor.
                # The proof for name overlaps must be checked.
                # The proof doesn't include this pairing. The
                # overlap occurs after composition with the pairing.
                # The proof to only some of the components returned
                # by the morphisms, in which case it its ssource and starget
                # are composed with (the pairing of) projections.

                # Consistency check along with getting the conversion
                # (renaming and deletion). The component morphisms are saved
                # in the same order they are executed. Their output is concatenated
                # and exactly corresponds to the target product.
                # Consistency equalities must always connect to the first
                # occurrence of the name.
                renaming: list[tuple[str, ProductParamName]] = []
                for i, subname in enumerate(name):
                    origname = typ.pos_to_name(i)
                    # This never needs to be (backend) type checked, hence can be used here.
                    # TODO: Check everywhere that such use is being followed.
                    pmor = typ.proj(origname).compose(mor)
                    n = subname or origname
                    if self._add_name(name_to_mor, mor_to_eq, n, pmor):
                        renaming.append((n if isinstance(n, str) else '', origname))
                # Based on having no assumptions about implementation and functions being pure
                # it makes sense to discard functions whose return values would be discarded.
                # The repeated functions are not fallbacks.
                if renaming:
                    components.append((True, ProductMor(typ, [
                        (new, typ.proj(old)) for new, old in renaming
                    ]).compose(mor)))
            else:
                target_params.append((name, typ))
                # No renaming here only deletions.
                if name:
                    if self._add_name(name_to_mor, mor_to_eq, name, mor):
                        components.append((False, mor))
                elif isinstance(typ, Product):
                    segment: list[str] = []
                    for subname in typ.names:
                        pmor = typ.proj(subname).compose(mor)
                        if self._add_name(name_to_mor, mor_to_eq, subname, pmor):
                            segment.append(subname if isinstance(subname, str) else '')

                    if segment:
                        if len(segment) == len(typ):
                            components.append((True, mor))
                        else:
                            components.append((True, ProductMor(typ, [
                                (m, typ.proj(m)) for m in segment
                            ]).compose(mor)))
                else:
                    if self._add_name(name_to_mor, mor_to_eq, typ, mor):
                        components.append((False, mor))

        target = Product(target_params)
        super().__init__(source, target)

    def eql(self, x: Mor):
        return super().eql(x) or (
            isinstance(x, ProductMor)
            and self.target.equiv(x.target)
            and all(
                u == v and s.eql(t)
                for (u, s), (v, t)
                in zip(self.components, x.components)
            )
        )
    
    def hint(self):
        return self.target, self.components
    
    def eval(
        self, x: object,
        check_source: bool = True,
        check_target: bool = True,
    ):
        # In the case of the local namespace (Product element) there
        # is a special composition that makes sure that linearity is respected.
        # Right before the return, the local namespace is made inmutable,
        # so that it can for example be safely returned, duplicated, etc.
        def _extend(res: MutableSequence[object], u: bool, m: Mor):
            r = m.eval(x)
            if u:
                assert(_isinstance_mutable_sequence_object(r))
                res.extend(r)
            else:
                res.append(r)

        if check_source:
            self.source.check(x)

        components = self.components
        if len(components) >= 1:
            first = components[0][1]
            if _is_identity(first) and _isinstance_mutable_sequence_object(x):
                for i in range(1, len(components)):
                    _extend(x, *components[i])
            return x

        _res: list[object] = []
        for c in components:
            _extend(_res, *c)

        return tuple(_res)
        
def _is_identity(mor: Mor):
    # This needs to be documented as part of a spec.
    return mor.hint() == ()
    

