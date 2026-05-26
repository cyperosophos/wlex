"""Private model of `cart` morphisms"""
from ..cells import Obj, Mor, Eq
from . import category
from .category import source, target, ssource, starget

TerminalMor = Mor
ObjObj = tuple[Obj, Obj]
Span = tuple[Mor, Mor]
ProductMor = tuple[Mor, Mor, Mor, Eq, Eq]
SpanEq = tuple[Span, Span, Eq, Eq]

def is_terminal_mor(mor: TerminalMor):
    """Models requirement of `cart.TerminalMor`"""
    t = target(mor)
    return t.identical(terminal(type(t)))

def is_span(s: Span):
    """Models requirement of `cart.Span`"""
    p, q = s
    return source(p).identical(source(q))

def is_product_mor(pm: ProductMor):
    """Models requirement of `cart.ProductMor`"""
    mor, p, q, p_eq, q_eq = pm
    _p, _q = product((target(p), target(q)))
    return (
        category.is_eq(p_eq) and category.is_eq(q_eq)
        and is_span((p, q))
        and source(mor).identical(source(p))
        and target(mor).identical(source(_p))
        and _p.compose(mor).same(ssource(p_eq))
        and p.same(starget(p_eq))
        and _q.compose(mor).same(ssource(q_eq))
        and q.same(starget(q_eq))
    )

def is_span_eq(se: SpanEq):
    """Models requirement of `cart.SpanEq`"""
    x, y, p_eq, q_eq = se
    x_p, x_q = x
    y_p, y_q = y
    p_s, p_t = category.eq_signature(p_eq)
    q_s, q_t = category.eq_signature(q_eq)
    return (
        category.is_eq(p_eq) and category.is_eq(q_eq)
        and is_span(x) and is_span(y)
        and source(x_p).identical(source(y_p)) # TODO: these may be superfluous
        and target(x_p).identical(target(y_p))
        and x_p.same(p_s) and y_p.same(p_t)
        and x_q.same(q_s) and y_q.same(q_t)
    )

def terminal(cls: type[Obj]) -> Obj:
    """Models morphism `cart.terminal`"""
    return cls.terminal()

def terminal_mor(obj: Obj) -> TerminalMor:
    """Models morphism `cart.terminal_mor`"""
    return obj.terminal_mor()

def terminal_mor_hat(obj: Obj):
    """Models hat equality for `cart.terminal_mor`"""
    return obj.identical(source(terminal_mor(obj)))

def terminal_mor_unique(mor: TerminalMor) -> Eq:
    """Private model of equality `cart.terminal_mor_unique`"""
    return mor.ref()

def terminal_mor_unique_hat(mor: TerminalMor):
    """Models hat equality for `cart.terminal_mor_unique`"""
    s, t = category.eq_signature(terminal_mor_unique(mor))
    return terminal_mor(source(mor)).same(s) and mor.same(t)

def product(xy: ObjObj) -> Span:
    """Models morphism `cart.product`"""
    x, y = xy
    obj = x.product(y)
    return obj.proj('x'), obj.proj('y')

def product_hat(xy: ObjObj):
    """Models hat equality for `cart.product`"""
    x, y = xy
    s_x, s_y = product(xy)
    return x.identical(target(s_x)) and y.identical(target(s_y))

def pairing(s: Span) -> ProductMor:
    """Private model of morphism `cart.pairing`"""
    p, q = s
    mor = p.pairing(q)
    return mor, p, q, p.ref(), q.ref()

def pairing_hat(s: Span):
    """Models hat equality for `cart.pairing`"""
    _, p_, q_, _, _ = pairing(s)
    p, q = s
    return p.same(p_) and q.same(q_)

def pairing_unique(pm: ProductMor) -> Eq:
    """Private model of morphism `cart.pairing_unique`"""
    # This cannot rely on `ref`, it can't be extensional, because one needs the
    # `p_eq`, `q_eq` equalities in order to get this equality. Analogously,
    # trans can't be based on `ref` because it requires equalities, which may be
    # intensional.
    mor, p, q, _, _ = pm
    return mor.pairing_unique(p, q)

def pairing_unique_hat(pm: ProductMor):
    """Models hat equality for `cart.pairing_unique`"""
    s, t = category.eq_signature(pairing_unique(pm))
    mor, p, q, _, _ = pm
    pmor, _, _, _, _ = pairing((p, q))
    return pmor.same(s) and mor.same(t)

def _pmy(se: SpanEq) -> ProductMor:
    x, y, p_eq, q_eq = se
    pm_mor, _, _, pm_p_eq, pm_q_eq = pairing(x)
    return (
        pm_mor, *y,
        category.trans((p_eq, pm_p_eq)),
        category.trans((q_eq, pm_q_eq)),
    )

def pairing_eq(se: SpanEq) -> Eq:
    """Private model of morphism `cart.pairing_eq`"""
    # This does not directly support the full variadic `pairing_eq` with labeled
    # components. One produces the equality associatively, then composes with a
    # "renamer" morphism (which allows repeated names if consistency proofs are
    # provided). The result of composing a pairing with a renamer must be a
    # pairing (in the sense of being an instance of the relevant class and not
    # of `Composition`). The problem with this approach is that the labelless
    # pairing would still need to be modified according to the consistency
    # proofs before being composed with the renamer. An alternative to this is
    # to just directly produce the pairing and pairing equality using the
    # labels, and just use the corresponding binary operations for type
    # checking.
    return category.sym(pairing_unique(_pmy(se)))

def pairing_eq_hat(se: SpanEq):
    """Models hat equality for `cart.pairing_eq`"""
    # This equality has in fact a proof. This means that the implementation here
    # consists solely of the equalities used in the proof. At this there is no
    # concept of verifying the proof. One simply knows empirically that, if
    # `pairing_eq_hat_proof` is True then so must be `pairing_eq_hat`.
    s, t = category.eq_signature(pairing_eq(se))
    x, y, _, _ = se
    x_mor, _, _, _, _ = pairing(x)
    y_mor, _, _, _, _ = pairing(y)
    return x_mor.same(s) and y_mor.same(t)

def pairing_eq_hat_proof(se: SpanEq):
    """Models proof of hat equality for `cart.pairing_eq`"""
    return (
        pairing_unique_hat(_pmy(se))
        and category.sym_hat(pairing_unique(_pmy(se)))
    )
