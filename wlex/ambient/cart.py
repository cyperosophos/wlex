from dataclasses import dataclass
from itertools import chain

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


class TProduct(Obj):
    x: Obj
    y: Obj

    class _Proj(Mor):
        def __repr__(self):
            return f'`t_product_proj {_an(self.name)}: {_an(self.source.name)} -> {_an(self.target.name)}`'
        
        def __eq__(self, x: Mor):
            if super().__eq__(x):
                return True
            if isinstance(x, TProduct._Proj):
                return (
                    self.source == x.source
                    and self.target == x.target
                )
            return False
        
        def eval(self, x, check_source=True, check_target=True):
            raise Error
        
        def set_eval(self, method):
            raise Error

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
        return self._Proj('$p', self, self.x)
    
    @property
    def q(self):
        return self._Proj('$q', self, self.y)
    
    def __iter__(self):
        return iter(('p', 'q'))
    
    def check(self, x):
        raise Error
    
    def set_check(self, method):
        raise Error
    
    def __str__(self):
        return f'({self.x}, {self.y})'
    
    def __repr__(self):
        return f'`t_product {self!s}`'

class Product(Obj):
    params: list[tuple[str | tuple[str], Obj]]
    flat: dict[str, tuple[int, Obj]]
    names: list[str]

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
                    self._add_name(sub_name, typ.pos_to_type(i))
                    #else:
                    #    raise Error
            #elif isinstance(name, str):
            else:
                if name:
                    self._add_name(name, typ)
                #elif isinstance(typ, Product):
                else:
                    self._add_names_from_type(typ)
                #else:
                #    raise Error
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
    
    def _check_tuple(self, x: tuple):
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
                    typ.check(x[self.flat[name][0]])
                else:
                    assert(isinstance(typ, Product))
                    typ._check_tuple(tuple(
                        x[self.flat[sub_name][1]]
                        for sub_name in name
                    ))
            else:
                assert(isinstance(typ, Product))
                typ._check_tuple(tuple(
                    x[self.flat[sub_name][1]]
                    for sub_name in typ.names
                ))

    def _check_dict(self, x: dict):
        for name, typ in self.params:
            if name:
                if isinstance(name, str):
                    typ.check(x.get(name) or x[self.flat[name][0]])
                else:
                    assert(isinstance(typ, Product))
                    typ._check_tuple(tuple(
                        x.get(sub_name) or x[self.flat[sub_name][1]]
                        for sub_name in name
                    ))
            else:
                assert(isinstance(typ, Product))
                typ._check_tuple(tuple(
                    x.get(sub_name) or x[self.flat[sub_name][1]]
                    for sub_name in typ.names
                ))
    
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
        
        if isinstance(x, tuple):
            self._check_tuple(x)
        elif isinstance(x, dict):
            self._check_dict(x)
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

class Pair(Mor):
    def __init__(self, p: Mor, q: Mor):
        source = Category.source(p)
        target = Product(Category.target(p), Category.target(q))
        # self.__init__

@dataclass
class ObjObj:
    x: Obj
    y: Obj

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

class Pairer:
    @classmethod
    def pair(
        cls,
        p: Mor | Unsourced | Eq | Obj,
        q: Mor | Unsourced | Eq | Obj,
    ) -> Mor | Unsourced | Eq:
        p, q = (
            Category.identity(m) if isinstance(m, Obj) else m
            for m in (p, q)
        )

        if isinstance(q, Unsourced):
            if isinstance(p, Eq):
                raise Error
        return UnsourcedPair(p, q)
    
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

    def el(self):
        pass

    def product(self, *args, **kwargs):
        if not args and not kwargs:
            return self.terminal
        
        all_args = chain(args, kwargs.items())
        params = []
        for arg in all_args:
            name, typ = _filter_arg(arg)
            acc = typ
            params.append((name, typ))
            break
        for arg in all_args:
            name, typ = _filter_arg(arg)
            acc = self.t_product((acc, typ))
            params.append((name, acc.y))
        return Product(params)

    def pair():
        pass

    def proj():
        pass

    @staticmethod
    def t_product(p: ObjObj) -> TProduct:
        # The whole type checking is done in the backend.
        # There's no way around it, since one doesn't know that
        # the function always returns TProduct.
        x, y = AttrDict.to_tuple(p, ObjObj)
        return TProduct(x, y)

    class _Producer(Producer):
        @staticmethod
        def t_product(p):
            return Cart.t_product(p)
        
    product = staticmethod(variadic(_Producer.product))

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

    def el(self):
        pass

    @property
    def terminal(self):
        return self.backend.terminal.eval(())
    
    def terminal_mor(self, x):
        return self.backend.terminal_mor.eval(x)
    
    def terminal_mor_unique(self, x):
        return self.backend.terminal_mor_unique.eval(x)