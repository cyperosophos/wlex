#from collections.abc import Sequence

from ..cells import Obj, Mor, Eq

TerminalMor = Mor
ObjObj = tuple[Obj, Obj]
Span = tuple[Mor, Mor]
ProductMor = tuple[Mor, Mor, Mor, Eq, Eq]
#SpanEq = tuple[Span, Span, Eq, Eq]

def terminal(cls: type[Obj]) -> Obj:
    return cls.terminal()

def terminal_mor(obj: Obj) -> TerminalMor:
    return obj.terminal_mor()

def terminal_mor_unique(mor: TerminalMor) -> Eq:
    # TODO: This requires appropriate Mor.__eq__
    return mor.ref()

def product(xy: ObjObj) -> Span:
    x, y = xy
    obj = x.product(y)
    return obj.proj('x'), obj.proj('y')

def pairing(s: Span) -> ProductMor:
    p, q = s
    pm = p.pairing(q)
    return pm, p, q, p.ref(), q.ref()

def pairing_unique(pm: ProductMor):
    # This cannot rely on ref, it can't be extensional, because
    # one needs the p_eq equalities in order get this equality.
    # Analogously, trans can't be based on ref because it requires
    # equalities, which can be extensional.
    return mor.pairing_unique(p, q)