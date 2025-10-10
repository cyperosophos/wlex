from typing import NamedTuple
from itertools import chain
from collections.abc import Sequence, Mapping, Sized #, Iterator

from ..theory.cart import Cart as BCart
from .cells import Obj, Mor, Eq
from .category import Category, Unsourced, CheckedCategory, Composable, Comp as BaseComp

class Error(Exception):
    pass

# The `:` helps distinguish product and pairing, as well as

class TerminalMor(Mor):
    # TODO: Should this be Pairing the way TerminalObj is Product?
    # We don't use NamedTuple for TerminalMor because (besides only one
    # parameter) it needs to define __eval__ and__eq__.
    # Note that cell __eq__ has been coded to raise a TypeError
    # when comparing with an instance of a different type.
    # Cells require sensible __eq__, Obj (for matching source and
    # target in composition), Mor (for proving equalities) and Eq
    # (for verifying proofs). In the case of NamedTuple subclasses,
    # one has equality with tuples, but not with lists, mappings, etc.
    # Still, one is able to prove intentional equality due to the
    # uniqueness of the pairing.
    # TODO: Verify the previous assertion.
    __slots__ = ()
    # eval returns ()
    def __init__(self, t: Obj):
        source = t
        # Not type checked, part of the definition of terminal_mor
        target = TerminalObj.T
        super().__init__(source, target)
    
    def eval(self, x, check_source=True, check_target=True):
        if check_source:
            Cart.source(self).check(x)
        # No need to check target
        return ()
    
    def __eq__(self, x: Mor):
        # __eq__ equality is extensional. The full uniqueness
        # (i.e. two morphisms with terminal object as target being equal)
        # is proved through terminal_mor_unique.
        if super().__eq__(x):
            return True
        return (
            self.source == x.source
            and TerminalObj.T == x.target
        )
    
    def __str__(self):
        # It's ok to not write ()[T], because the contexts where this
        # will show up will often make the type clear.
        return f'()'

    def __repr__(self):
        return f'`terminal_mor {self!s}[{self.source}]`'
    
class UnsourcedTerminalMor(Unsourced):
    __slots__ = ()

    def with_source(self, source: Obj):
        return source.terminal_mor()
    
    def __str__(self):
        return '()'
    
    def __repr__(self):
        return '`unsourced_terminal_mor`'

class TerminalMorUnique(Eq):
    __slots__ = ()

    def __init__(self, mor: Mor):
        ssource = Cart.terminal_mor(Cart.source(mor))
        starget = mor
        super().__init__(ssource, starget)

    @property
    def proven(self):
        return True
    
    def assume(self):
        raise Error
    
    def __str__(self):
        # One simply uses [] instead of something like {} regardless
        # of naturality, functoriality, etc., since these properties
        # are not part of the type checking system, i.e. they don't
        # belong to the theory, except as properties of specific
        # functors and nat trans. These properties occur a posteriori.
        # This is like a macro. The same applies to interface functors, etc.
        # The idea is that constructs of the theory have no special syntax.
        # So f @ g could be written as comp[f, g], etc. All the backend type checking
        # is supported. One may in fact define macros.
        # TODO: Should interface functors use a different syntax?
        return f'terminal_mor_unique[{self.starget.source}]'
    
    def __repr__(self):
        return f'`terminal_mor_unique {self!s}`'

# Recall that Product is used when building theory, i.e.
# the return type of ambient.product.
# ambient.t_product takes Product and returns TProduct.
# TProduct instance must pass the backend type checking
# for Span, which is an instance of Product with equalizer.
# Hence, TProduct instance doesn't provide a check method
# (for objects to be considered to have the TProduct instance
# as type) it simply passes Product type checking.
# More specfically (X, Y) is of type Product(x=Obj, y=Obj),
# TProduct(X, Y) is of type Product(p=Mor, q=Mor) with equalizer
# (as supported by Lex, namely Span).
# $p and $q used in theory are not TProductProj but just the
# regular Proj for Product (no use for eval).
# Also no clear use for __eq__.
# At most, one uses t_product within product, because the former
# is type checked by backend.

# TProduct is the actual common source of the Span returned
# by t_product. True product. The public method product
# takes care of parameter naming and calls t_product for
# its own type checking. An instance of TProduct must be
# a Span (a pair of Mors p, q sharing the same source).
# TProduct is not used for type checking by the backend.
# __eq__ and _Proj are needed for purity of t_product.
# The Mor values that make up the Span are not evaluated
# since they are not used by the backend, however they
# are used for type checking (e.g. in compositions).

class Product(Obj, Mapping):
    __slots__ = 'params', 'flat', 'names'
    weakened = True
    _terminal: 'Product'
    # TODO: Make immutable? Remove superfluous type hints from
    # function signatures (functions with type checking).
    params: list[tuple[str, Obj] | tuple[tuple[str], 'Product']]
    _flat: dict[str | type, tuple[int, Obj]]
    names: list[str | type]

    def proj(*args):
        # This needs pairing
        pass

    def __new__(cls, params):
        if not params:
            if not hasattr(cls, '_terminal'):
                cls._terminal = super().__new__(cls)
            return cls._terminal
        return super().__new__(cls)

    def __getitem__(self, key):
        if isinstance(key, int):
            return self.pos_to_type(key)
        return self.name_to_type(key)

    def __iter__(self):
        return iter(self.names)

    def __contains__(self, key):
        if isinstance(key, int):
            return 0 <= key < len(self)
        return key in self._flat
    
    def includes(self, prod: 'Product') -> bool:
        if not isinstance(prod, Product):
            raise TypeError
        return all(
            name in self._flat
            and self.name_to_type(name) == prod.name_to_type(name)
            for name in prod.names
        )

    def name_to_type(self, name):
        return self._flat[name][1]

    def _add_name(self, name, typ: Obj):
        if name in self._flat:
            pos, t = self._flat[name]
            # TODO: Make sure types are always checked to be equal
            # not identical. This is needed in order to compare Product.
            if t != typ:
                raise ValueError
        else:
            self._flat[name] = (len(self._flat), typ)

    def pos_to_type(self, pos):
        return self._flat[self.names[pos]][1]
    
    def pos_to_name(self, pos):
        return self.names[pos]

    def pos_to_name_and_type(self, pos):
        name = self.names[pos]
        return name, self._flat[name][1]
    
    def _add_names_from_type(self, typ: 'Product'):
        for subname, (pos, t) in typ._flat.items():
            self._add_name(subname, t)

    def __init__(
            self,
            params: list[tuple[str, Obj] | tuple[tuple[str], 'Product']],
            weakened=True
        ):
        self.params = params
        self._flat = dict() # maps to position

        if not weakened:
            self.weakened = False

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
            else:
                if not isinstance(typ, Obj):
                    raise TypeError
                if name: # name is str
                    self._add_name(name, typ)
                elif isinstance(typ, Product):
                    self._add_names_from_type(typ)
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
        self.names = list(self._flat.keys())

    def __eq__(self, v):
        return self is v or (
            isinstance(v, Product)
            and self.weakened == v.weakened
            and self.params == v.params
        )
            # all(
            #     n == m and s.same_as_obj(t)
            #     for (n, s), (m, t)
            #     in zip(self.params, v.params)
            # )
    
    def __len__(self):
        return len(self._flat)
    
    def _check(self, x: Sequence, _get):
        # Handle the mandatory flattening of nameless parameters in x that provide
        # subparameters. This is done with args and kwargs whose keys
        # are tuples.
        # TODO: Fix the following in the sample syntax (wlex files) and theory code where needed?
        # One cannot directly determine the position of a parameter due to flattening.
        # Hence nameless parameters must be product types (i.e. provide suparameters).
        # Repeating the product type without names has no effect, i.e. it is the same as
        # including the product type only once.
        # If the overriding name is a tuple, names must be provided for all subparams.
        # TODO: If it is a dict (or k, v list), then only overridden names.
        for name, typ in self.params:
            if name:
                if isinstance(name, str):
                    typ.check(_get(x, name))
                else:
                    # Handle empty subname by replacing it with the
                    # name in the product param.
                    typ._check(
                        self._sequence_from_subnames(x, name, typ, _get),
                        self._get_from_sequence,
                    )
            elif isinstance(typ, Product):
                typ._check(
                    self._sequence_from_type(x, typ, _get),
                    self._get_from_sequence,
                )
            else:
                typ.check(_get(x, typ))

    def _get_from_sequence(self, x: Sequence, name):
        # No requirements are made here about x passing the type check.
        # We don't allow index instead of name, because flattening makes indices too complicated.
        return x[self._flat[name][0]]

    def _get_from_mapping(self, x: Mapping, name):
        return x.get(name) or x[self._flat[name][0]]

    def eval_proj(self, x: Mapping | Sequence, name):
        # No need to check length, since this would be part of actual eval method in Proj.
        # Being Mapping | Sequence is guarantied by the type checking of Proj.eval since its
        # parameter is of type Product(...).

        if isinstance(x, Mapping):
            return self._get_from_mapping(x, name)
        return self._get_from_sequence(x, name)
    
    def check(self, x):
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

        if isinstance(x, Sized):
            length = len(x)
        else:
            length = 1

        if self.weakened:
            if length < len(self._flat):
                raise Error
        elif length != len(self._flat):
            raise Error
        
        if isinstance(x, Mapping):
            self._check(x, self._get_from_mapping)
        elif isinstance(x, Sequence):
            self._check(x, self._get_from_sequence)
        else:
            # TODO: Projection must handle an argument like x (not a collection).
            if self._flat:
                self.pos_to_type(0).check(x)
            else:
                if self.weakened:
                    return
                raise Error
            
    def _sequence_from_subnames(x, subnames, typ: 'Product', _get):
        return [
            _get(
                x,
                subname or typ.pos_to_name(i),
            ) for i, subname in enumerate(subnames)
        ]
    
    def _sequence_from_type(x, typ: 'Product', _get):
        return [
            _get(x, subname)
            for subname in typ.names
        ]
        
    def _check_eq(self, x, y, _x_get, _y_get):
        _gfs = self._get_from_sequence
        for name, typ in self.params:
            if name:
                if isinstance(name, str):
                    typ.check_eql(
                        _x_get(x, name),
                        _y_get(y, name),
                    )
                else:
                    typ._check_eq(
                        self._sequence_from_type(x, name, typ, _x_get),
                        self._sequence_from_type(y, name, typ, _y_get),
                        _gfs, _gfs,
                    )
            elif isinstance(typ, Product):
                typ._check_eq(
                    self._sequence_from_type(x, typ, _x_get),
                    self._sequence_from_type(y, typ, _y_get),
                    _gfs, _gfs,
                )
            else:
                typ.check_eql(
                    _x_get(x, typ),
                    _y_get(y, typ),
                )
        
    def check_eql(self, x, y):
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
        _x_get, _y_get = (
            self._get_from_mapping
            if isinstance(v, Mapping)
            else self._get_from_sequence
            for v in (x, y)
        )

        x, y = (
            v if isinstance(v, Sequence) else (v,)
            for v in (x, y)
        )

        self._check_eq(x, y, _x_get, _y_get)

    def __str__(self):
        def format_param(name, typ):
            if name:
                if isinstance(name, str):
                    fname = name
                else:
                    fname = f'({', '.join(name)})'
                return f'{fname}: {typ}'
            else:
                return f':{typ}'

        return f'({', '.join(f'{format_param(*p)}' for p in self.params)})'
    
    def __repr__(self):
        return f'`product {self!s}`'
    
# class TProj?
    
class Proj(Mor):
    def __init__(self, key, source):
        self.key = key
        target = self._get_target(source)
        super().__init__(None, source, target)

    def _get_target(self, source: Obj):
        if isinstance(source, Product):
            # Get the type corresponding to self.key.
            return source.name_to_type(self.key)
        elif source is self.key:
            # source must be self.key. Return it unchanged.
            # source and self.key are required to be identical.
            # This seems to work because it doesn't make sense for
            # key to be a Product. If one needs to extract multiple attributes,
            # one uses a pairing of projections.
            return source
        else:
            raise Error
    
    def eval(self, x, check_source=True, check_target=True):
        source = Cart.source(self)
        if isinstance(source, Product):
            if check_source:
                source.check(x)
            y = source.eval_proj(x, self.key) # Must occur after check_source
            if check_target and not check_source:
                # If source has been checked, there is no need to check the target.
                target = Cart.target(self)
                target.check(y)
            return y
        else:
            # Same as category.Id
            if check_source or check_target:
                source.check(x)
            return x
        
    def __eq__(self, x: Mor):
        if super().__eq__(x):
            return True
        return (
            isinstance(x, Proj)
            and self.key == x.key
            and Cart.source(self) == Cart.source(x)
        )

    #def __str__(self):
    #    pass

    #def __repr__(self):
    #    pass

class UnsourcedProj(Unsourced):
    def __init__(self, key):
        self.key = key

    def with_source(self, source):
        return Proj(self.key, source)

class TProductMor(Mor, Mapping):
    p: Mor
    q: Mor
    p_eq: Eq
    q_eq: Eq

    _keys = (Mor, 'p', 'q', 'p_eq', 'q_eq')

    # Implementing __eq__ here makes product_mor_unique partially extensional.
    # Cf. TerminalMor.__eq__
    def __eq__(self, x: Mor):
        return (
            isinstance(x, TProductMor)
            and self.p == x.p
            and self.q == x.q
        )

    class _ProjEq(Eq):
        proj_name: str

        def __init__(self, pmor):
            # TODO: Is type checking required here and in other similar calls?
            ssource = Cart.t_compose(getattr(self._pt(), self.proj_name), self)
            starget = getattr(self, self.proj_name)
            super().__init__(None, ssource, starget)

        @property
        def proven(self):
            # TODO: Should this be implemented? cf. _Proj.eval.
            return True
        
        def assume(self):
            raise Error

    class _PProjEq(Eq):
        proj_name = 'p'

    class _QProjEq(Eq):
        proj_name = 'q'

    def __init__(self, p: Mor, q: Mor):
        # TODO: Allow nameless param Mor. The way to do this is by allowing
        # implicit type conversion. This works different to Unsourced.
        # Source is determined, but it doesn't coincide with the target
        # of the precomposed morphism. One still needs unsourced proj,
        # specifically the ones with type names. These work like the identity
        # on the type itself. One possibility then is to precomposed all morphisms
        # with such unsourced projections. One still needs to make sure that
        # backend based type checking remains relevant for ensuring that source
        # and target coincide.
        self.p = p
        self.q = q
        source = Cart.source(p)
        target = self._pt()
        super().__init__(None, source, target)

    def _pt(self) -> TProduct:
        # Recall that TProduct is both the Span and the source of the Span
        return Cart.t_product(Cart.target(self.p), Cart.target(self.q))

    @property
    def p_eq(self):
        # this Eq must have proven = True, just like there must be an eval for
        # the pairing. Cf. TerminalMorUnique.
        # TODO: No type checking of t_compose, etc.? 
        return self._PProjEq(self)
    
    @property
    def q_eq(self):
        return self._QProjEq(self)

    __iter__ = TProduct.__iter__
    
    def __len__(self):
        return 5
    
    def __getitem__(self, key):
        if key not in self._keys:
            raise KeyError
        # is comparison doesn't handle (one type) Product equality.
        # Does that matter?
        if key is Mor:
            return self
        else:
            return getattr(self, key)

    # __str__
    # __repr__
    
    #def __iter__(self): # -> Iterator[Mor, Mor]:
    #    return iter(getattr(self, name) for name in self.__slots__)

    # Sequence doesn't implement __eq__!

class WithAttrs(Sequence):
    attr_names: tuple

    #def head(self):
    #    raise NotImplementedError

    def __getitem__(self, i):
        if i < 0:
            i += len(self)
        if i < 0:
            raise IndexError
        if i == 0:
            return self
        return getattr(self, self.attr_names[i-1])

    def __len__(self):
        return 1 + len(self.attr_names)
    
    def __iter__(self):
        return iter((self, *(getattr(self, n) for n in self.attr_names)))

class ObjObj(NamedTuple):
    x: Obj
    y: Obj

class Span(NamedTuple):
    # Subclassing does not allow Span to be a NamedTuple
    # TODO: Remove need for __slots__ using metaclass?
    #attrs = __slots__ = 'p', 'q'
    p: Mor
    q: Mor

    # TODO: How does one keep type annotations for unpacking without this?
    #def __iter__(self):
    #    return iter((self.p, self.q))

class ProductMorEq(Eq):
    proj_name: str

    def __init__(self, pm: 'ProductMor'):
        n = self.proj_name
        mor = pm
        prod_p: Mor = getattr(pm.pt, n)
        ssource = prod_p.compose(mor)
        starget = getattr(pm, n)
        super().__init__(ssource, starget)

    @property
    def proven(self):
        return True
    
class ProductMorPEq(Eq):
    proj_name = 'p'

class ProductMorQEq(Eq):
    proj_name = 'q'

class ProductMor(Mor, WithAttrs):
    __slots__ = 'p', 'q', 'p_eq', 'q_eq'

    # Span
    p: Mor
    q: Mor

    p_eq: Eq
    q_eq: Eq

    attr_names = 'p', 'q', 'p_eq', 'q_eq'
    # p_eq and q_eq are true just like the instance of ProductMor
    # has eval, etc.

    def __init__(self, p: Mor, q: Mor):
        source = p.source
        pt = p.target.product(q.target)
        self.pt = pt
        target = pt.p.source
        super().__init__(source, target)
        self.p = p
        self.q = q

    @property
    def p_eq(self):
        # There must be no need to use self[0] here.
        mor = self
        return Eq(self.pt.p.compose(mor), self.p)
        #return ProductMorPEq(self)
    
    @property
    def q_eq(self):
        mor = self
        return Eq(self.pt.q.compose(mor), self.q)
        #return ProductMorQEq(self)

    # No eval. Pairing, not this, is used by backend type checking.
    
#def foo(pm: ProductMor):
#    m, p, q, p_eq, q_eq = pm


class SpanEq(NamedTuple):
    x: Span
    y: Span
    p_eq: Eq
    q_eq: Eq
    
class UnsourcedPair:
    def __init__(self, p: Unsourced, q: Unsourced):
        self.p = p
        self.q = q

    def with_source(self, source):
        # TODO: Why not allowing backend type checking?
        return 

class Pairer:
    # Somehow this should produce an AttrDict or similar.

    @classmethod
    def pair(
        cls,
        p: Mor | Unsourced | Eq | Obj,
        q: Mor | Unsourced | Eq | Obj,
    ) -> Mor | Unsourced | Eq:
        p, q = (
            Cart.identity(m) if isinstance(m, Obj) else m
            for m in (p, q)
        )

        if isinstance(p, Unsourced):
            if isinstance(q, Unsourced):
                return UnsourcedPair(p, q)

            if isinstance(q, Eq):
                s = Cart.source(Cart.ssource(q))
                p = Cart.ref(p.with_source(s))
                return cls.pairing_eq((p, q))
            
            p = p.with_source(Cart.source(q))
            return cls.pairing((p, q))

        if isinstance(p, Eq):
            if isinstance(q, Unsourced):
                s = Cart.source(Cart.ssource(p))
                q = Cart.ref(q.with_source(s))
                return cls.pairing_eq((p, q))
            
            if isinstance(q, Eq):
                return cls.pairing_eq((p, q))
            
            q = Cart.ref(q)
            return cls.pairing_eq((p, q))
        
        if isinstance(q, Unsourced):
            q = q.with_source(Cart.source(p))
            return cls.pairing((p, q))
        
        if isinstance(q, Eq):
            p = Cart.ref(p)
            return cls.pairing_eq((p, q))
        
        return cls.pairing((p, q))
    
    @staticmethod
    def pairing(p: Span) -> ProductMor:
        # This means t_pair.
        pass

    @staticmethod
    def pairing_eq(p: SpanEq) -> Eq:
        pass
    
def _filter_arg(arg):
    if isinstance(arg, tuple):
        name, typ = arg
        if isinstance(name, tuple):
            for subname in name:
                if not isinstance(subname, str):
                    raise TypeError
                if not subname:
                    raise ValueError
        elif not isinstance(name, str):
            raise TypeError
    elif isinstance(arg, Obj):
        name = ''
        typ = arg
    else:
        raise TypeError
    return name, typ

# WeakenedMor is extensionally equal to the composition of self.orig
# with the appropriate projection or pairing of projections.
# The reflected equality must be handled in Comp.__eq__, along
# with p_eq and q_eq of pairing, or rather Comp.__eq__ defers
# to this __eq__. Something analogous must occur with coprojections.
# Being equal to self.orig does not imply being equal to self,
# as the signatures would not coincide. If is better to just use Comp
# No need to implement everything again, and the weakening morphism
# is the only extra data.

def weaken_mor(f: Mor, source: Obj) -> Mor:
    if not (isinstance(source, Product) and source.weakened):
        return f
    s = f.source
    if s == source:
        return f
    #if isinstance(source, Product):
    #if not source.weakened:
    #    raise ValueError
    #else:
    #    raise TypeError
    if isinstance(s, Product):
        g = source.proj(*s)
    else:
        # This checks that s is in source.
        g = source.proj(s) # Projection with source
        #if source.includes(s):
        #    pass
        #else:
        #    raise ValueError
    # if s in source:
    #     g = source.proj(s) # Projection with source.
    # else:
    #     raise ValueError
    
    return f.compose(g)

def weaken_eq(d: Eq, source: Obj) -> Eq:
    if not (isinstance(source, Product) and source.weakened):
        return d
    s = d.ssource.source
    if s == source:
        return d
    if isinstance(s, Product):
        e = source.proj(*s).ref()
    else:
        e = source.proj(s).ref()
    return d.compose_eq(e)


# class WeakenedMor(Mor):
#     __slots__ = 'orig',
#     orig: Mor

#     def __str__(self):
#         return f'{self.orig}'
    
#     def __repr__(self):
#         return f'`weakened_mor {self!s}: {self.source} -> {self.orig.source} -> {self.target}`'

#     def __init__(self, orig: Mor, source):
#         if isinstance(source, Product):
#             if not source.weakened:
#                 raise ValueError
#         else:
#             raise TypeError
#         target = orig.target
#         osource = orig.source
#         if isinstance(osource, Product) and not source.includes(osource):
#             raise ValueError
#         if osource not in source:
#             raise ValueError
#         super().__init__(source, target)

#     def _weakening(self):
#         # This is needed in __eq__, in order to be able to compare with Comp.
#         # Projection or pairing projections
#         return ...

#     def eval(self, x, check_source=True, check_target=True):
#         return self.orig.eval(x, check_source, check_target)

#     def __eq__(self, x: Mor):

#         if super().__eq__(x):
#             return True
#         if isinstance(x, WeakenedMor):
#             return (
#                 self.source == x.source
#                 and self.orig == x.orig
#             )
#         if isinstance(x, Comp):
#             return (
#                 self.orig == x.f
#                 and self._weakening()  == x.g
#             )
#         return False


class Comp(BaseComp):
    pass

class Cart(Category):
    # This is static like all other theory methods
    terminal = Product()

    def el(
            self, name,
            target: Mor | Obj,
            value: Mor | Unsourced | Obj | None = None,
            proof: Eq | Mor | Obj | None = None,
        ):
        # Supports HatMor but, since the source is the terminal
        # object, this is superfluous.
        # We use type checked self.terminal, because it would have
        # to be used without the syntax sugar.
        return self.mor(name, self.terminal, target, value, proof)

    def pairing(self, *args):
        pass

    #def proj():
    #    pass

    def t_product(self, p: ObjObj) -> Span:
        # According to the type checking done by backend
        # The source of t_product must by of type Product
        # with params x, y, e.g. dict(x=x, y=y), (x, y).
        # The target must be of type Span, which is a subset
        # of Product (as supported by ambient Lex) with params
        # p, q.
        # What about AttrDict? Should it be supported by Product type checking??
        # AttrDict is already a dict, so it is supported.
        # The whole type checking is done in the backend.
        # There's no way around it, since one doesn't know that
        # the function always returns TProduct.
        x, y = p
        return x.product(y)
    
    def t_pairing(self, s: Span) -> ProductMor:
        # Remember: there is not point in type checking intermediate
        # steps. The construction is correct as long as it coincide with
        # the signature.
        p, q = s
        return p.pairing(q)
    
    def product(self, *args, **kwargs):
        if not args and not kwargs:
            return self.terminal
        
        all_args = chain(args, kwargs.items())
        params = []
        acc = None
        for arg in all_args:
            name, typ = _filter_arg(arg)
            acc = self.checked_product(acc, typ)
            params.append((name, typ))
        return type(self.terminal)(params)
    
    def checked_product(self, acc, typ):
        return acc

    @staticmethod
    def terminal_mor(t: Obj) -> Mor:
        # TODO: t.terminal_mor
        return TerminalMor(t)
    
    @staticmethod
    def terminal_mor_unique(mor: Mor) -> Eq:
        # TODO: t.terminal_mor_unique
        return TerminalMorUnique(mor)

class CheckedCart(CheckedCategory):
    unchecked_cls = Cart
    backend: BCart
    unchecked: Cart

    def set_semantics(self, backend: BCart):
        super().set_semantics(backend.C)
        u = self.unchecked
        backend.terminal.set_eval(lambda x: u.terminal)
        backend.terminal_mor.set_eval(u.terminal_mor)
        backend.terminal_mor_unique.set_eval(u.terminal_mor_unique)
        backend.product.set_eval(u.t_product)
        backend.pairing.set_eval(u.pairing)
        backend.pairing_unique.set_eval(u.pairing_unique)

    el = Cart.el
    product = Cart.product

    def checked_product(self, acc, typ):
        if acc:
            return self.t_product((acc, typ))
        return typ

    def t_product(self, x):
        return self.backend.product.eval(x)

    @property
    def terminal(self):
        return self.backend.terminal.eval(())
    
    def terminal_mor(self, x):
        return self.backend.terminal_mor.eval(x)
    
    def terminal_mor_unique(self, x):
        return self.backend.terminal_mor_unique.eval(x)

    def _init_producer(self):
        class _Producer(Producer):
            @staticmethod
            def t_product(p):
                return self.t_product(p)
  
        self.product = _Producer.product