from ..theory.lex import Lex as BLex
from ..ambient import Obj, Mor, Eq
from ..ambient.cells import filter_name as _an
from .category import Category, variadic, Unsourced

class Error(Exception):
    pass

# TODO: Consider using __slots__

class TProduct(Obj):
    x: Obj
    y: Obj

    class _Proj(Mor):
        def __repr__(self):
            return f'`proj {_an(self.name)}: {_an(self.source.name)} -> {_an(self.target.name)}`'
        
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
    # takes care of parameter naming and alls t_product for
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
    args: tuple[Obj]
    kwargs: dict[str, Obj]

    def __init__(self, *args, **kwargs):
        super().__init__(None)
        self.args = args
        self.kwargs = kwargs

    def __eq__(self, v):
        return (
            isinstance(v, Product)
            and self.args == v.args
            and self.kwargs == v.kwargs
        )
    
    def __len__(self):
        return len(self.args) + len(self.kwargs)
    
    def set_check(self, method):
        raise Error
    
    def check(self, x):
        # x can be category.AttrDict, tuple or dict.
        # AttrDict is simply treated as dict.
        if isinstance(x, tuple):
            if len(x) != len(self):
                raise Error
            for i, t in enumerate(self.args):
                t.check(x[i])
            l = len(self.args)
            for i, t in enumerate(self.kwargs.values()):
                t.check(x[i + l])
            return
        
        if isinstance(x, dict):
            kwargs = x.copy()
            for i, t in enumerate(self.args):
                t.check(kwargs.pop(i))
            for k, t in self.kwargs.items():
                t.check(kwargs.pop(k))
            if kwargs:
                raise Error

    def __str__(self):
        # TODO: See fn associativy in category.wlex for an example
        # of colliding names (g in this case) and unpacking.
        return (
            f'({', '.join(f'{x}' for x in self.args)}, '
            f'{', '.join(f'{k}: {v}' for k, v in self.kwargs)})'
        )
    
    def __repr__(self):
        return f'`product {self!s}`'

class Product(Obj):
    x: Obj
    y: Obj

    def __init__(self, x: Obj, y: Obj):
        super().__init__(None)
        self.x = x
        self.y = y

    def check(self, z):
        # What about product of multiple objects?
        # Support a semantic approach less tied to the theory.
        # Include parameter names.
        pass

    def set_check(self, method):
        raise Error
    
    def __str__(self):
        return f'({self.x}, {self.y})'
    
    def __repr__(self):
        return f'product {self!s}'

class Pair(Mor):
    def __init__(self, p: Mor, q: Mor):
        source = Category.source(p)
        target = Product(Category.target(p), Category.target(q))
        # self.__init__


class Producer:
    pass

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

class Lex(Category):
    def pair():
        pass