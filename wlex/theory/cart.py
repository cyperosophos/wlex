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

    RetSec: MetaObj
    proj_section: MetaMor

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
            pairing_eq=ctx.mor_refs['pairing_eq'],
            RetSec=ctx.obj_refs['RetSec'],
            proj_section=ctx.mor_refs['proj_section'],
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
    imp = ctx.imp
    ix = ctx.ix

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
    _, _terminal_mor_unique_hat = ctx.mor('terminal_mor_unique', prim.terminal_mor_unique, (
        TerminalMor, Eq,
        p(c(Mor, terminal_mor, source), Mor),
        eq,
    ))
    _terminal_mor_unique_hat(prim.terminal_mor_unique_hat)
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
    pt = c(ix(product), p(c(target, p_), c(target, q)), Span)
    p_eq, q_eq, mor = (proj(n) for n in ('p_eq', 'q_eq', 'mor'))
    # `source @ $mor = source @ $p` is implied by the requirement.
    # `target @ $mor = source @ $p @ pt` is a requirement of the first
    # requirement.
    ProductMorP = req(prod(
        ('mor', Mor), ('p', Mor),
        ('p_eq', Eq),
    ), (
        p(c(ix(compose), p(c(p_, pt), mor)), p_),
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
        p(c(ix(compose), p(c(q, pt), mor)), q),
        c(eq, q_eq),
    )))

    pairing, _pairing_hat = ctx.mor('pairing', prim.pairing, (
        Span, c(Span, ProductMor),
    ))
    _pairing_hat(prim.pairing_hat)
    pairing_unique, _pairing_unique_hat = ctx.mor('pairing_unique', prim.pairing_unique, (
        ProductMor, Eq,
        p(c(mor, pairing), mor),
        eq,
    ))
    _pairing_unique_hat(prim.pairing_unique_hat)

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

    pm_mor, pm_p_eq, pm_q_eq = (proj(n) for n in ('pm_mor', 'pm_p_eq', 'pm_q_eq'))
    # Notice that relabeling does not preserve equivalence, so it must never be implicit.
    # TODO: !!! Complete missing requirements as they start appearing! e.g. trans @ p(...), compose @ p(...)
    pmy = imp(
        ('', l(c(pairing, x), ('pm_mor', '', '', 'pm_p_eq', 'q_eq', 'pm_q_eq'))),
        ('', p(
            ('mor', pm_mor), ('', y),
            ('p_eq', c(ix(C.S.S.P.trans), p(p_eq, pm_p_eq))),
            ('q_eq', c(ix(C.S.S.P.trans), p(q_eq, pm_q_eq))),
        )),
    )

    _, _pairing_eq_hat = ctx.mor(
        'pairing_eq',
        c(C.S.S.sym, pairing_unique, pmy),
        (
            SpanEq, Eq,
            p(c(mor, pairing, x), c(mor, pairing, y)),
            eq,
        ),
    )
    # Implicit application of p_eq for mor @ pmy = mor @ pairing @ x
    _pairing_eq_hat(c(
        t(
            c(
                p(
                    t(c(C.S.source, C.S.S.sym), C.S.target),
                    t(c(C.S.target, C.S.S.sym), C.S.source),
                ),
                pairing_unique,
            ),
            c(
                p(C.S.target, C.S.source),
                pairing_unique,
            ),
            mor,
        ),
        pmy,
        SpanEq, # TODO: Check that taking out this arg will produce an error (due to pmy being a transformation).
    ))

    f, g, h = (proj(n) for n in 'fgh')
    dnp = c(ix(ProductMor), p(
        c(ix(compose), p(mor, h)), c(ix(compose), p(p_, h)), c(ix(compose), p(q, h)),
        c(ix(C.S.S.P.trans), p(
            c(C.compose_eq, p(p_eq, h)),
            c(C.associativity, p(c(p_, pt), c(mor, h))),
        )),
        c(ix(C.S.S.P.trans), p(
            c(C.compose_eq, p(q_eq, h)),
            c(C.associativity, p(c(q, pt), c(mor, h))),
        )),
    ), p(
        ('', c(ix(pairing), p(f, g))),
        ('h', h),
    ))
    _, _diagonal_natural_hat = ctx.mor(
        'diag_natural',
        c(pairing_unique, dnp), (
            req(prod(
                ('', l(Span, ('f', 'g'))), ('h', Mor),
            ), (
                c(target, h), c(source, f),
            )), Eq,
            p(
                c(mor, ix(pairing), p(c(ix(compose), p(f, h)), c(ix(compose), p(g, h)))),
                c(ix(compose), p(c(mor, ix(pairing), p(f, g)), h)),
            ), eq,
        ),
    )

    # TODO: Is this proof needed below??
    #t(c(p_, ix(pairing), p(f, g)), f)
    _diagonal_natural_hat(t(
        #c(eq, diag_natural),
        c(p( # Notice that ix on projection produces terminal morphism!
            c(mor, pairing),
            mor,
        ), dnp), # TODO: Is this link missing?? This probably accomplished by simplification (disregading expensive mors)!
        p(
            c(mor, pairing, dnp), # ix(pairing) doesn't work here because its source is Span not ProductMor
            c(mor, dnp),
        ),
        p(
            c(mor, ix(pairing), p( # TODO: possible missing link! Common source gets determined by signature.
                c(ix(compose), p(f, h)),
                c(ix(compose), p(g, h)),
            )),
            c(ix(compose), p(c(mor, ix(pairing), p(f, g)), h)),
        )
    ))

    r, s, e = (proj(n) for n in 'rse')
    RetSec = ctx.define('RetSec', req(prod(
        ('r', Mor), ('s', Mor),
        ('e', Eq),
    ), (
        p(c(compose, p(r, s)), c(C.identity, source, s)),
        c(eq, e),
    )))

    el = proj('el')
    pid = c(pairing, p(
        c(C.identity, x),
        c(compose, p(el, c(terminal_mor, x))),
    ))
    _ = c(p_, ctx.ref(product), p(x, t(y, c(target, el))))
    ctx.eq(c(compose, t(
        p(t( # TODO: Missing links?
            c(p_, ctx.ref(product), p(x, t(y, c(target, el)))), # TODO: this will probably give an error due to transformations in the last factor.
            c(p_, pt, p(
                c(C.identity, x),
                c(compose, p(el, c(terminal_mor, x))),
            )),
            c(p_, pt, pid),
        ), c(mor, pid)), # TODO: Naturality of the diagonal, see coment above.
        c(p(c(p_, pt), mor), pid),
    )))
    ctx.eq(t(
        c(C.identity, t(
            c(source, mor, pid),
            c(source, C.identity, x),
            x,
        )), # Possible missing link ^pairing, see (f, g) above
        c(p_, pid),
    ))
    _ = ctx.mor(
        'proj_section', c(ix(RetSec), p(
            c(p_, product),
            c(mor, pid),
            c(p_eq, pid),
        )),
        (
            req(prod(
                ('el', Mor), ('x', Obj), ('y', Obj),
            ), (
                c(source, el),
                terminal,
            ), (
                c(target, el),
                y,
            )),
            RetSec,
        )
    )

    return ctx
