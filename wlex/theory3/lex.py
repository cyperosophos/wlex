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

from .cart import (
    CartStub, CartTheory, Cart,
)

@dataclass(frozen=True)
class LexStub:
    C: _s[CartStub]

    equalizer: _o[MorStub]
    equalizer_hat: _o[EqStub]
    equalizer_pairing: _o[MorStub]
    equalizer_pairing_hat: _o[EqStub]
    equalizer_pairing_unique: _o[MorStub]
    equalizer_pairing_unique_hat: _o[EqStub]

@dataclass(frozen=True)
class LexTheory(Theory):
    C: CartTheory
    Obj: MetaObj
    Mor: MetaObj
    Eq: MetaObj
    eq: MetaMor
    source: MetaMor
    target: MetaMor
    compose: MetaMor

    Parallel: MetaObj
    Fork: MetaObj

    equalizer: MetaMor

    EqualizerMor: MetaObj

    equalizer_pairing: MetaMor
    equalizer_pairing_unique: MetaMor

    ForkEq: MetaObj
    equalizer_pairing_eq: MetaMor

    @classmethod
    def from_ctx(cls, ctx: Context[Self]):
        return cls(
            C=_ot(ctx.sub_refs['C'], CartTheory),
            Obj=ctx.obj_refs['Obj'],
            Mor=ctx.obj_refs['Mor'],
            Eq=ctx.obj_refs['Eq'],
            eq=ctx.mor_refs['eq'],
            source=ctx.mor_refs['source'],
            target=ctx.mor_refs['target'],
            compose=ctx.mor_refs['compose'],
            Parallel=ctx.obj_refs['Parallel'],
            Fork=ctx.obj_refs['Fork'],
            equalizer=ctx.mor_refs['equalizer'],
            EqualizerMor=ctx.obj_refs['EqualizerMor'],
            equalizer_pairing=ctx.mor_refs['equalizer_pairing'],
            equalizer_pairing_unique=ctx.mor_refs['equalizer_pairing_unique'],
            ForkEq=ctx.obj_refs['ForkEq'],
            equalizer_pairing_eq=ctx.mor_refs['equalizer_pairing_eq'],
        )

def Lex(stub: _u[LexStub]):
    ctx = LexContext(LexTheory)
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

    C = ctx.sub('C', Cart(prim.C))
    _ = ctx.define('Obj', C.Obj)
    Mor = ctx.define('Mor', C.Mor)
    Eq = ctx.define('Eq', C.Eq)
    eq = ctx.define('eq', C.eq)
    source = ctx.define('source', C.source)
    target = ctx.define('target', C.target)
    compose = ctx.define('compose', C.compose)

    i_, j = (proj(n) for n in 'ij')
    Parallel = ctx.define('Parallel', req(
        prod(('i', Mor), ('j', Mor)),
        (
            c(p(source, target), i_),
            c(p(source, target), j),
        )
    ))
    p_, fe, mor, eq_ = (proj(n) for n in ('p', 'fe', 'mor', 'eq'))
    Fork0 = ctx.define('Fork', req(
        prod(('p', Mor), ('', Parallel)),
        (c(source, i_), c(target, p_)),
    ))
    ctx.eq(t(
        c(source, j, Fork0), c(source, i_),
        c(target, p_),
    ))
    Fork = ctx.define('Fork', req(
        prod(('', Fork0), ('fe', Eq)),
        (p(
            c(ix(compose), p(i, p_)),
            c(ix(compose), p(j, p_)),
        ), c(eq, fe)),
    ))

    equalizer, _equalizer_hat = ctx.mor('equalizer', prim.equalizer, (
        Parallel, c(Parallel, Fork),
    ))
    _equalizer_hat(prim.equalizer_hat)

    meqp = c(p_, equalizer)
    EqualizerMor = ctx.define('EqualizerMor', ctx.req(
        prod(('mor', Mor), ('', Fork), ('eq', Eq)),
        (c(source, mor), c(source, p)),
        (c(target, mor), c(source, meqp)),
        (
            p(c(ix(compose), p(meqp, mor)), p_),
            c(eq, eq_),
        ),
    ))

    equalizer_pairing, _equalizer_pairing_hat = ctx.mor(
        'equalizer_pairing', prim.equalizer_pairing,
        (
            Fork, c(Fork, EqualizerMor),
        ),
    )
    _equalizer_pairing_hat(prim.equalizer_pairing_hat)

    equalizer_pairing_unique, _equalizer_pairing_unique_hat = ctx.mor(
        'equalizer_pairing_unique', prim.equalizer_pairing_unique,
        (
            EqualizerMor, Eq,
            p(c(mor, equalizer_pairing), mor),
            eq,
        ),
    )

    x, y, c_, d, e = (proj(n) for n in 'xycde')
    ForkEq = ctx.define('ForkEq', req(prod(
        ('', l(Fork, ('x', 'i', 'j', 'c'))),
        ('', l(Fork, ('y', 'i', 'j', 'd'))),
        ('e', Eq),
    ), (
        p(x, y),
        c(eq, e),
    )))

    em_mor, em_eq = (proj(n) for n in ('em_mor', 'em_eq'))
    emy = imp(
        ('', l(c(ix(equalizer_pairing), p(x, i, j, c_)), ('em_mor', '', '', '', '', 'em_eq'))),
        ('', p(
            ('mor', em_mor), ('p', y), ('i', i), ('j', j), ('fe', d),
            ('eq', c(ix(C.C.S.S.P.trans), p(e, em_eq))),
        ))
    )

    _, _equalizer_pairing_eq_hat = ctx.mor(
        'equalizer_pairing_eq',
        c(C.C.S.S.sym, equalizer_pairing_unique, emy),
        (
            ForkEq, Eq,
            p(
                c(mor, equalizer_pairing, p(x, i, j, c_)),
                c(mor, equalizer_pairing, p(y, i, j, d)),
            ),
            eq
        )
    )

    _equalizer_pairing_eq_hat(c(
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

    return ctx
