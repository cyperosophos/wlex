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

# TODO: support for canonical iso, conversion. The way to hande this is with
# a dict like the one for equalities, and `canonincal` flag of the iso
# method.

@dataclass(frozen=True)
class CartStub:
    C: _s[CategoryStub]

    terminal: _o[MorStub]
    terminal_mor: _o[MorStub]
    terminal_mor_hat: _o[EqStub]
    terminal_mor_ihat: _o[EqStub]
    product: _o[MorStub]
    product_hat: _o[EqStub]
    pairing: _o[MorStub]
    pairing_hat: _o[EqStub]
    pairing_ihat: _o[EqStub]
    pairing_eq: _o[MorStub]
    pairing_eq_hat: _o[EqStub]
    pairing_eq_ihat: _o[EqStub]

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

    Span: MetaObj
    product: MetaMor
    Pairing: MetaObj
    pairing: MetaMor

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
            terminal_mor=ctx.mor_refs['TerminalMor'],
            Span=ctx.obj_refs['Span'],
            product=ctx.mor_refs['product'],
            Pairing=ctx.obj_refs['Pairing'],
            pairing=ctx.mor_refs['Pairing'],
            SpanEq=ctx.obj_refs['SpanEq'],
            pairing_eq=ctx.mor_refs['pairing_eq'],
            RetSec=ctx.obj_refs['RetSec'],
            proj_section=ctx.mor_refs['proj_section'],
        )

def Cart(stub: _u[CartStub]):
    ctx = LexContext(CartTheory)
    prim = _o.prim(stub)
    c = ctx.c
    #t = ctx.t
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
    _, _terminal_mor_hat, _terminal_mor_ihat = ctx.iso(
        'TerminalMor', prim.terminal_mor, (
        Obj, TerminalMor, source,
    ))
    _terminal_mor_hat(prim.terminal_mor_hat)
    _terminal_mor_ihat(prim.terminal_mor_ihat)
    p_, q = (proj(n) for n in 'pq')
    mor = proj('mor')

    Span = req(prod(('p', Mor), ('q', Mor)), (
        c(source, p_),
        c(source, q),
    ))
    SpanEq = req(prod(('p', Eq), ('q', Eq)), (
        c(source, C.S.S.source, p_),
        c(source, C.S.S.source, q),
    ))

    product, _product_hat = ctx.mor('product', prim.product, (
        prod(('x', Obj), ('y', Obj)), Span,
        i, p(c(target, p_), c(target, q)),
    ))
    _product_hat(prim.product_hat)
    Pairing = req(
        prod(('mor', Mor), ('x', Obj), ('y', Obj)),
        (target, product),
    )
    PairingEq = req(
        prod(('mor', Eq), ('x', Obj), ('y', Obj)),
        (c(target, C.S.S.source), product),
    )

    _, _pairing_hat, _pairing_ihat = ctx.iso(
        'Pairing', prim.pairing,
        (Span, Pairing, p(
            ('p', c(ix(compose), p(c(p_, product), mor))),
            ('q', c(ix(compose), p(c(q, product), mor))),
        )),
    )
    _pairing_hat(prim.pairing_hat)
    _pairing_ihat(prim.pairing_ihat)

    _, _pairing_eq_hat, _pairing_eq_ihat = ctx.iso(
        'PairingEq', prim.pairing_eq,
        (SpanEq, PairingEq, p(
            ('p', c(C.compose_eq, p(c(C.S.S.P.ref, p_, product), mor))),
            ('q', c(C.compose_eq, p(c(C.S.S.P.ref, p_, product), mor))),
        )),
    )
    _pairing_eq_hat(prim.pairing_eq_hat)
    _pairing_eq_ihat(prim.pairing_eq_ihat)

    f, g, h, k = (ctx.proj(n) for n in 'fghk')
    _, _diag_natural_hat = ctx.mor(
        'diag_natural',
        imp(
            p(('k', c(mor, Pairing, p(('p', f), ('q', g))))),
            c(mor, PairingEq, p(
                ('p', c(C.associativity, p(p_, k, h))),
                ('q', c(C.associativity, p(q, k, h))),
            )),
        ), (
            req(prod(
                ('', l(Span, ('f', 'g'))), ('h', Mor),
            ), (
                c(target, h), c(source, f),
            )), Eq,
            p(
                c(ix(compose), p(c(mor, Pairing, p(('p', f), ('q', g))), h)),
                c(mor, Pairing, p(('p', c(ix(compose), p(f, h))), ('q', c(ix(compose), p(g, h))))),
            ), eq,
        ),
    )
    _diag_natural_hat(None) # TODO: Missing proof! Handle ix in proof.

    return ctx
