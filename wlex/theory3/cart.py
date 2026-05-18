# pylint: disable=C0103, R0902, C0115, C0114
from dataclasses import dataclass
from typing import Self

from wlex.ambient.cells import (
    Obj as MetaObj, Mor as MetaMor, MorStub, EqStub,
)
from wlex.ambient.category import (
    Context, Theory, Once as _o, OnceStub as _s, OnceUpdate as _u,
    of_type as _ot,
)
from wlex.ambient.lex import LexContext

from .category import (
    CategoryStub, CategoryTheory, Category,
)

@dataclass(frozen=True)
class CartStub:
    C: _s[CategoryStub]

    terminal: _o[MorStub]
    terminal_mor: _o[MorStub]
    terminal_mor_hat: _o[EqStub]
    terminal_mor_unique: _o[MorStub]
    terminal_mor_unique_hat: _o[EqStub]
    product: _o[MorStub]
    product_hat: _o[EqStub]
    pairing: _o[MorStub]
    pairing_hat: _o[EqStub]
    pairing_unique: _o[MorStub]
    pairing_unique_hat: _o[EqStub]

@dataclass(frozen=True)
class CartTheory(Theory):
    C: CategoryTheory
    Obj: MetaObj
    Mor: MetaObj
    Eq: MetaObj
    eq: MetaMor
    source: MetaMor
    target: MetaMor
    compose: MetaMor
    terminal: MetaMor
    TerminalMor: MetaObj
    terminal_mor: MetaMor
    terminal_mor_unique: MetaMor

    Span: MetaObj
    product: MetaMor
    ProductMor: MetaObj

    pairing: MetaMor
    pairing_unique: MetaMor

    SpanEq: MetaObj
    pairing_eq: MetaMor

    @classmethod
    def from_ctx(cls, ctx: Context[Self]):
        return cls(
            C=_ot(ctx.sub_refs['C'], CategoryTheory),
            Obj=ctx.obj_refs['Obj'],
            Mor=ctx.obj_refs['Mor'],
            Eq=ctx.obj_refs['Eq'],
            eq=ctx.mor_refs['Mor'],
            source=ctx.mor_refs['source'],
            target=ctx.mor_refs['target'],
            compose=ctx.mor_refs['compose'],
            terminal=ctx.mor_refs['terminal'],
            TerminalMor=ctx.obj_refs['TerminalMor'],
            terminal_mor=ctx.mor_refs['terminal_mor'],
            terminal_mor_unique=ctx.mor_refs['terminal_mor_unique'],
            Span=ctx.obj_refs['Span'],
            product=ctx.mor_refs['product'],
            ProductMor=ctx.obj_refs['ProductMor'],
            pairing=ctx.mor_refs['pairing'],
            pairing_unique=ctx.mor_refs['pairing_unique'],
            SpanEq=ctx.obj_refs['SpanEq'],
            pairing_eq=ctx.mor_refs['pairing_eq']
        )

def Cart(stub: _u[CartStub]):
    ctx = LexContext(CartTheory)
    prim = _o.prim(stub)
    c = ctx.c
    t = ctx.t
    p = ctx.pair
    prod = ctx.prod
    req = ctx.req
    proj = ctx.proj
    i = ctx.id
    l = ctx.l

    C = ctx.sub('C', Category(prim.C))
    Obj = ctx.define('Obj', C.Obj)
    Mor = ctx.define('Mor', C.Mor)
    Eq = ctx.define('Eq', C.Eq)
    eq = ctx.define('eq', C.eq)
    source = ctx.define('source', C.source)
    target = ctx.define('target', C.target)
    compose = ctx.define('compose', C.compose)
    terminal = ctx.el('terminal', prim.terminal, Obj)
    TerminalMor = ctx.define('TerminalMor', req(Mor, (
        target,
        c(terminal, ctx.tm),
    )))
    terminal_mor, _terminal_mor_hat = ctx.mor('terminal_mor', prim.terminal_mor, (
        Obj, c(source, TerminalMor),
    ))
    _terminal_mor_hat(prim.terminal_mor_hat)
    terminal_mor_unique = ctx.mor('terminal_mor_unique', prim.terminal_mor_unique, (
        TerminalMor, Eq,
        p(c(Mor, terminal_mor, source), Mor),
        eq,
    ))
    p_, q = (proj(n) for n in 'pq')
    Span = req(prod(('p', Mor), ('q', Mor)), (
        c(source, p_),
        c(source, q),
    ))
    product, _product_hat = ctx.mor('product', prim.product, (
        prod(('x', Obj), ('y', Obj)), Span,
        i, p(c(target, p_), c(target, q)),
    ))
    _product_hat(prim.product_hat)
    pt = c(product, p(c(target, p_), c(target, q)), Span)
    p_eq, q_eq, mor = (proj(n) for n in ('p_eq', 'q_eq', 'mor'))
    # `source @ $mor = source @ $p` is implied by the requirement.
    # `target @ $mor = source @ $p @ pt` is a requirement of the first
    # requirement.
    ProductMorP = req(prod(
        ('mor', Mor), ('p', Mor),
        ('p_eq', Eq),
    ), (
        p(c(compose, p(c(p_, pt), mor)), p_),
        c(eq, p_eq),
    ))
    ctx.eq(t(
        c(target, mor), c(source, p_, pt),
        c(t(c(source, p_, Span), c(source, q)), pt),
    ))
    # TODO: Rewrite private/cart.py based on this approach of
    # summarized requirements. For example, instead of checking the
    # superfluous Composable requirements use the actual public compose
    # function, which handles the type-checking.
    # TODO: Is there a problem with not using labels in `private`, since
    # cart obj uses labels for elements (dict instead of tuple)?
    ProductMor = ctx.define('ProductMor', req(prod(
        ('', ProductMorP), ('', Span),
        ('q_eq', Eq),
    ), (
        p(c(compose, p(c(q, pt), mor)), q),
        c(eq, q_eq),
    )))

    pairing, _pairing_hat = ctx.mor('pairing', prim.pairing, (
        Span, c(Span, ProductMor),
    ))
    _pairing_hat(prim.pairing_hat)
    pairing_unique = ctx.mor('pairing_unique', prim.pairing_unique, (
        ProductMor, Eq,
        p(c(mor, pairing), mor),
        eq,
    ))

    x, y = (ctx.proj(n) for n in 'xy')
    SpanEq = ctx.define('SpanEq', req(prod(
        ('x', Span), ('y', Span),
        ('p_eq', Eq), ('q_eq', Eq),
    ), (
        p(c(p_, x), c(p_, y)),
        c(eq, p_eq),
    ), (
        p(c(q, x), c(q, y)),
        c(eq, q_eq),
    )))

    # TODO: This requires imperative composition.
    pmy = c(p(
        ('mor', mor), ('', y),
        ('p_eq', c(C.S.S.P.trans, p(
            c(p_eq, SpanEq),
            c(p_eq, ProductMor),
        ))),
        ('q_eq', c(C.S.S.P.trans, p(
            c(q_eq, SpanEq),
            c(q_eq, ProductMor),
        ))),
    ), pairing, x)
