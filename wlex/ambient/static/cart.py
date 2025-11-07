"""Static model of `cart` morphisms

Here static means that there is here only the minimal type checking supported
through type annotations.
"""
from ..cells import Obj, Mor, Eq
from . import category

TerminalMor = Mor
ObjObj = tuple[Obj, Obj]
Span = tuple[Mor, Mor]
ProductMor = tuple[Mor, Mor, Mor, Eq, Eq]
SpanEq = tuple[Span, Span, Eq, Eq]

# TODO: Make sure all hat equalities are checked in `dependent`

def terminal(cls: type[Obj]) -> Obj:
    """Static model of morphism `cart.terminal`"""
    return cls.terminal()

def terminal_mor(obj: Obj) -> TerminalMor:
    """Static model of morphism `cart.terminal_mor`"""
    return obj.terminal_mor()

def terminal_mor_unique(mor: TerminalMor) -> Eq:
    """Static model of equality `cart.terminal_mor_unique`"""
    # TODO: This requires appropriate Mor.__eq__
    return mor.ref()

def product(xy: ObjObj) -> Span:
    """Static model morphism `cart.product`"""
    x, y = xy
    obj = x.product(y)
    return obj.proj('x'), obj.proj('y')

def pairing(s: Span) -> ProductMor:
    """Static model of morphism `cart.pairing`"""
    p, q = s
    mor = p.pairing(q)
    return mor, p, q, p.ref(), q.ref()

def pairing_unique(pm: ProductMor) -> Eq:
    """Static model of morphism `cart.pairing_unique`"""
    # This cannot rely on `ref`, it can't be extensional, because one needs the
    # `p_eq`, `q_eq` equalities in order to get this equality. Analogously,
    # trans can't be based on `ref` because it requires equalities, which may be
    # intensional.
    mor, p, q, _, _ = pm
    return mor.pairing_unique(p, q)

def pairing_eq(se: SpanEq) -> Eq:
    """Static model of morphism `cart.pairing_eq`"""
    x, y, p_eq, q_eq = se
    pm_mor, _, _, pm_p_eq, pm_q_eq = pairing(x)
    return category.sym(pairing_unique((
        pm_mor, *y,
        category.trans((p_eq, pm_p_eq)),
        category.trans((q_eq, pm_q_eq)),
    )))
