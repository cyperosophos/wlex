from dataclasses import dataclass
from itertools import chain
from collections.abc import Sequence, Mapping

from ..theory.cart import Cart as BCart
from . import Obj, Mor, Eq, Checked
from .cells import filter_name as _an
from .category import Category, variadic, Unsourced, AttrDict, CheckedCategory

class Error(Exception):
    pass

# TODO: Consider using __slots__

class TerminalObj(Obj):
    def __init__(self):
        super().__init__(None)

    def __eq__(self, v):
        return isinstance(v, TerminalObj)

    def check(self, x):
        if x != ():
            raise Error
    
    def set_check(self, method):
        raise Error
    
    def __str__(self):
        return f'()'
    
    def __repr__(self):
        return f'`terminal_obj {self!s}`'
    

class TerminalMor(Mor):
    # eval returns ()
    def __init__(self, t: Obj):
        source = t
        target = Cart.terminal
        super().__init__(None, source, target)
    
    def eval(self, x, check_source=True, check_target=True):
        if check_source:
            Cart.source(self).check(x)
        # No need to check target
        return ()
    
    def set_eval(self, method):
        raise Error
    
    def __eq__(self, x: Mor):
        # __eq__ equality is extensional. The full uniqueness
        # (i.e. two morphisms with terminal object as target being equal)
        # is proved through terminal_mor_unique.
        return (
            Cart.source(self) == Cart.source(x)
            and Cart.target(x) == Cart.terminal
        )
    
    # __str__
    # __repr__

class TerminalMorUnique(Eq):
    def __init__(self, mor: Mor):
        ssource = Cart.terminal_mor(Cart.source(mor))
        starget = mor
        super().__init__(mor.name, ssource, starget)

    @property
    def proven(self):
        return True
    
    def assume(self):
        raise Error
    
    # __str__
    # __repr__

class TProduct(Obj, Mapping):
    x: Obj
    y: Obj

    _keys = ('p', 'q')

    class _Proj(Mor):
        proj_name: str

        def __init__(self, prod):
            source = prod
            target = getattr(prod, self.proj_name)
            super().__init__(None, source, target)

        def __repr__(self):
            return f'`t_product_proj {_an(self.name)}: {_an(self.source.name)} -> {_an(self.target.name)}`'
        
        def __eq__(self, x: Mor):
            if super().__eq__(x):
                return True
            if isinstance(x, type(self)):
                return (
                    self.source == x.source
                    and self.target == x.target
                )
            return False
        
        def eval(self, v, check_source=True, check_target=True):
            if check_source:
                pass
            return getattr(v, self.proj_name)
        
        def set_eval(self, method):
            raise Error
        
    class _XProj(_Proj):
        proj_name = 'x'

    class _YProj(_Proj):
        proj_name = 'y'

    # This is the actual common source of the Span returned
    # by t_product. True product. The public method product
    # takes care of parameter naming and calls t_product for
    # its own type checking. An instance of TProduct must be
    # a Span (a pair of Mors p, q sharing the same source).
    # TProduct is not used for type checking by the backend.
    # __eq__ and _Proj are needed for purity of t_product.
    # The Mor values that make up the Span are not evaluated
    # since they are not used by the backend, however they
    # are used for type checking (e.g. in compositions).
    def __init__(self, x: Obj, y: Obj):
        super().__init__(None)
        self.x = x
        self.y = y

    def __eq__(self, v):
        return (
            isinstance(v, TProduct)
            and self.x == v.x
            and self.y == v.y
        )
    
    @property
    def p(self):
        # The projection here is called p, but that doesn't mean
        # the attr in the semantics is called p.
        return self._XProj(self)
    
    @property
    def q(self):
        return self._YProj(self)
    
    def __iter__(self):
        return iter(self._keys)
    
    def __len__(self):
        return 2
    
    def __getitem__(self, key):
        if key not in self._keys:
            raise KeyError
        return getattr(self, key)
    
    def check(self, x):
        # The line that says
        # backend.product.set_eval(u.t_product)
        # uses Product not TProduct for type checking.
        # TODO: Or use this in the Product.check?
        raise Error
    
    def set_check(self, method):
        raise Error
    
    def __str__(self):
        return f'({self.x}, {self.y})'
    
    def __repr__(self):
        return f'`t_product {self!s}`'

class Product(Obj):
    params: list[tuple[str | tuple[str], Obj]]
    flat: dict[str | type, tuple[int, Obj]]
    names: list[str | type]

    def name_to_type(self, name):
        return self.flat[name][1]

    def _add_name(self, name, typ):
        if name in self.flat:
            pos, t = self.flat[name]
            # TODO: Make sure types are always checked to be equal
            # not identical. This is needed in order to compare Product.
            if t != typ:
                raise Error
        else:
            self.flat[name] = (len(self.flat), typ)

    def pos_to_type(self, pos):
        return self.flat[self.names[pos]][1]

    def pos_to_name_and_type(self, pos):
        name = self.names[pos]
        return name, self.flat[name][1]
    
    def _add_names_from_type(self, typ: 'Product'):
        for sub_name, typ in typ.flat.items():
            self._add_name(sub_name, typ)

    def __init__(self, params: list[tuple[str | tuple[str], Obj]]):
        super().__init__(None)
        self.params = params
        self.flat = dict() # maps to position

        for arg in params:
            #if isinstance(arg, tuple):
            name, typ = arg
            # Shallow overriding of names
            if isinstance(name, tuple):
                #if not isinstance(typ, Product) or len(name) != len(typ):
                #    raise Error
                for i, sub_name in enumerate(name):
                    #if isinstance(sub_name, str) and sub_name:
                    # Repeated sub_name is allowed.
                    assert(isinstance(typ, Product))
                    if sub_name:
                        self._add_name(sub_name, typ.pos_to_type(i))
                    else:
                        # An empty subname will keep the original subname.
                        # This means that, in the case of a named product subparam,
                        # no further flattening will occured, it will remain as a Product param.
                        self._add_name(*typ.pos_to_name_and_type(i))
                    #else:
                    #    raise Error
            #elif isinstance(name, str):
            else:
                if name:
                    self._add_name(name, typ)
                elif isinstance(typ, Product):
                    self._add_names_from_type(typ)
                else:
                    # The type is the name
                    self._add_name(typ, typ)
            #else:
            #    raise Error
            # param gets appended even if the key is repeated.
            #self.params.append(arg)
            # Nameless arg allowed after kwarg
            #elif isinstance(arg, Product):
                # TODO: This assumes other limits will be subclasses
                # of Product. But this doesn't make a lot of sense in
                # the case of an equalizer. The solution seems to treat
                # subsets (equalizers) of Product as Product.
                # Recall however that the equality of the equalizer requires
                # using a name for the single parameter.
                # Also one may use a single parameter product in order to
                # set the name of a parameter before a nameless product parameter.
                # Hence treat equalizers (when needed) as single parameter products.
            #    self._add_names_from_type(arg)
            #    self.params.append(('', arg))
            #else:
            #    raise Error
               
        self.names = list(self.flat.keys())

    def __eq__(self, v):
        return (
            isinstance(v, Product)
            and self.params == v.params
        )
    
    def __len__(self):
        return len(self.flat)
    
    def set_check(self, method):
        raise Error
    
    def _check_sequence(self, x: Sequence):
        # Handle the mandatory flattening of nameless parameters in x that provide
        # subparameters. This is done with args and kwargs whose keys
        # are tuples.
        # TODO: Fix the following in the sample syntax (wlex files) and theory code where needed.
        # One cannot directly determine the position of a parameter due to flattening.
        # Hence nameless parameters must be product types (i.e. provide suparameters).
        # Repeating the product type without names has no effect, i.e. it is the same as
        # including the product type only once.
        # If the overriding name is a tuple, names must be provided for all subparams.
        # TODO: If it is a dict (or k, v list), then only overridden names.
        for name, typ in self.params:
            if name:
                if isinstance(name, str):
                    typ.check(self._get_from_sequence(x, name))
                else:
                    # This assertion should have been checked in __init__.
                    assert(isinstance(typ, Product))
                    typ._check_sequence(
                        self._get_from_sequence(x, sub_name)
                        for sub_name in name
                    )
            elif isinstance(typ, Product):
                typ._check_sequence(
                    self._get_from_sequence(x, sub_name)
                    for sub_name in typ.names
                )
            else:
                typ.check(self._get_from_sequence(x, typ))

    def _get_from_sequence(self, x: Sequence, name):
        # No requirements are made here about x passing the type check.
        # We don't allow index instead of name, because flattening makes indices too complicated.
        return x[self.flat[name][0]]

    def _get_from_mapping(self, x: Mapping, name):
        return x.get(name) or x[self.flat[name][0]]

    def _check_mapping(self, x: Mapping):
        for name, typ in self.params:
            if name:
                if isinstance(name, str):
                    typ.check(self._get_from_mapping(x, name))
                else:
                    assert(isinstance(typ, Product))
                    typ._check_sequence(
                        self._get_from_mapping(x, sub_name)
                        for sub_name in name
                    )
            elif isinstance(typ, Product):
                typ._check_sequence(
                    self._get_from_mapping(x, sub_name)
                    for sub_name in typ.names
                )
            else:
                typ.check(self._get_from_mapping(x, typ))

    def eval_proj(self, x, name):
        # No need to check length, since this would be part of actual eval method in Proj.
        
        if isinstance(x, Mapping):
            return self._get_from_mapping(x, name)
        elif isinstance(x, Sequence):
            return self._get_from_sequence(x, name)
        else:
            raise Error
    
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
        if len(x) != len(self):
            raise Error
        
        if isinstance(x, Mapping):
            self._check_mapping(x)
        elif isinstance(x, Sequence):
            self._check_sequence(x)
        else:
            raise Error

    def __str__(self):
        def format_param(name, typ):
            if name:
                if isinstance(name, str):
                    fname = name
                else:
                    fname = f'({', '.join(name)})'
                return f'{fname}: {typ}'
            else:
                return f'{typ}'

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
        
    def set_eval(self, method):
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

class ProductMor(Mor):
    pass

@dataclass
class ObjObj:
    x: Obj
    y: Obj

@dataclass
class Span:
    p: Mor
    q: Mor

@dataclass
class SpanEq:
    p_eq: Eq
    q_eq: Eq

class Producer:
    @classmethod
    def product(cls, *args, **kwargs):
        if not args and not kwargs:
            return Cart.terminal
        
        all_args = chain(args, kwargs.items())
        params = []
        for arg in all_args:
            name, typ = _filter_arg(arg)
            acc = typ
            params.append((name, typ))
            break
        for arg in all_args:
            name, typ = _filter_arg(arg)
            acc = cls.t_product((acc, typ))
            params.append((name, acc.y))
        return Product(params)
    
    @staticmethod
    def t_product(p: ObjObj) -> TProduct:
        raise NotImplementedError
    
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
            if not isinstance(typ, Product) or len(name) != len(typ):
                raise Error
            for sub_name in name:
                if not (isinstance(sub_name, str) and sub_name):
                    raise Error
        elif isinstance(name, str):
            if not (name or isinstance(typ, Product)):
                raise Error
        else:
            raise Error
    elif isinstance(arg, Product):
        name = ''
        typ = arg
    else:
        raise Error
    return name, typ


class Cart(Category):
    # This is static like all other theory methods
    terminal = TerminalObj()

    def el(
            self, name,
            target: Mor | Obj,
            value: Mor | Unsourced | Obj | None = None,
            proof: Eq | Mor | Obj | None = None,
        ):
        # Supports HatMor but, since the source is the terminal
        # object, this is superfluous.
        return self.mor(name, self.terminal, target, value, proof)

    def pair():
        pass

    def proj():
        pass

    @staticmethod
    def t_product(p: ObjObj) -> TProduct:
        # According to the type checking done by backend
        # The source of t_product must by of type Product
        # with params x, y, e.g. dict(x=x, y=y), (x, y).
        # The target must be of type Span, which is a subset
        # of Product (as supported by ambient Lex) with params
        # p, q. Is this what __iter__ is for??
        # What about AttrDict? Should it be supported by Product type checking??
        # AttrDict is already a dict, so it is supported.
        # The whole type checking is done in the backend.
        # There's no way around it, since one doesn't know that
        # the function always returns TProduct.
        x, y = AttrDict.to_tuple(p, ObjObj)
        return TProduct(x, y)

    class _Producer(Producer):
        @staticmethod
        def t_product(p):
            return Cart.t_product(p)
        
    product = staticmethod(_Producer.product)

    @staticmethod
    def terminal_mor(t: Obj) -> Mor:
        return TerminalMor(t)
    
    @staticmethod
    def terminal_mor_unique(mor: Mor) -> Eq:
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