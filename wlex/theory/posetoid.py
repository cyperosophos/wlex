# pylint: disable=C0103, R0902, C0115, C0114
from dataclasses import dataclass
from typing import Self

from wlex.ambient.cells import (
    Obj, Mor, MorStub, EqStub,
)
from wlex.ambient.category import (
    Context, Theory, Once as _o, OnceStub as _s, OnceUpdate as _u,
    of_type as _ot,
)
from wlex.ambient.lex import LexContext

from .quiver import (
    BasicQuiverStub, BasicQuiverTheory, BasicQuiver,
)

@dataclass(frozen=True)
class PosetoidStub:
    Q: _s[BasicQuiverStub]
    ref: _o[MorStub]
    ref_hat: _o[EqStub]
    trans: _o[MorStub]
    trans_hat: _o[EqStub]

@dataclass(frozen=True)
class PosetoidTheory(Theory):
    Q: BasicQuiverTheory
    El: Obj
    Rel: Obj
    source: Mor
    target: Mor
    Path: Obj
    ref: Mor
    trans: Mor

    @classmethod
    def from_ctx(cls, ctx: Context[Self]):
        return cls(
            Q=_ot(ctx.sub_refs['Q'], BasicQuiverTheory),
            El=ctx.obj_refs['El'],
            Rel=ctx.obj_refs['Rel'],
            source=ctx.mor_refs['source'],
            target=ctx.mor_refs['target'],
            Path=ctx.obj_refs['Path'],
            ref=ctx.mor_refs['ref'],
            trans=ctx.mor_refs['trans'],
        )

@dataclass(frozen=True)
class SetoidStub:
    P: _s[PosetoidStub]
    sym: _o[MorStub]
    sym_hat: _o[EqStub]

@dataclass(frozen=True)
class SetoidTheory(Theory):
    P: PosetoidTheory
    Eq: Obj
    source: Mor
    target: Mor
    sym: Mor

    @classmethod
    def from_ctx(cls, ctx: Context[Self]):
        return cls(
            P=_ot(ctx.sub_refs['P'], PosetoidTheory),
            Eq=ctx.obj_refs['Eq'],
            source=ctx.mor_refs['source'],
            target=ctx.mor_refs['target'],
            sym=ctx.mor_refs['sym'],
        )

@dataclass(frozen=True)
class CongruenceStub:
    S: _s[SetoidStub]
    unique: _o[MorStub]
    unique_hat: _o[EqStub]

@dataclass(frozen=True)
class CongruenceTheory(Theory):
    S: SetoidTheory
    Eq: Obj
    source: Mor
    target: Mor
    eq: Mor
    unique: Mor

    @classmethod
    def from_ctx(cls, ctx: Context[Self]):
        return cls(
            S=_ot(ctx.sub_refs['S'], SetoidTheory),
            Eq=ctx.obj_refs['Eq'],
            source=ctx.mor_refs['source'],
            target=ctx.mor_refs['target'],
            eq=ctx.mor_refs['eq'],
            unique=ctx.mor_refs['unique'],
        )

def Posetoid(stub: _u[PosetoidStub]):
    ctx = LexContext(PosetoidTheory)
    prim = _o.prim(stub)
    c = ctx.c
    p = ctx.pair
    prod = ctx.prod
    req = ctx.req
    proj = ctx.proj
    i = ctx.id

    Q = ctx.sub('Q', BasicQuiver(prim.Q))
    El = ctx.define('El', Q.Node)
    Rel = ctx.define('Edge', Q.Edge)
    source = ctx.define('source', Q.source)
    target = ctx.define('target', Q.target)

    Path = ctx.define('Path', req(
        prod(('f', Rel), ('g', Rel)),
        (c(source, proj('f')), c(target, proj('g'))),
    ))

    _, _ref_hat = ctx.mor('ref', prim.ref, (
        c(p(i, i), El),
        p(source, target),
    ))
    _ref_hat(prim.ref_hat)

    _, _trans_hat = ctx.mor('trans', prim.trans, (
        c(p(
            c(source, proj('g')),
            c(target, proj('f')),
        ), Path),
        p(source, target),
    ))
    _trans_hat(prim.trans_hat)

    return ctx

def Setoid(stub: _u[SetoidStub]):
    ctx = LexContext(SetoidTheory)
    prim = _o.prim(stub)
    p = ctx.pair

    P = ctx.sub('P', Posetoid(prim.P))
    _ = ctx.define('Eq', P.Rel)
    source = ctx.define('source', P.source)
    target = ctx.define('target', P.target)
    _, _sym_hat = ctx.mor('sym', prim.sym, (
        p(source, target),
        p(target, source),
    ))
    _sym_hat(prim.sym_hat)

    return ctx

def Congruence(stub: _u[CongruenceStub]):
    # TODO: Notice that define and mor overlap.
    ctx = LexContext(CongruenceTheory)
    prim = _o.prim(stub)
    c = ctx.c
    p = ctx.pair
    prod = ctx.prod
    req = ctx.req
    proj = ctx.proj
    i = ctx.id

    S = ctx.sub('S', Setoid(prim.S))
    Eq = ctx.define('Eq', S.Eq)
    source = ctx.define('source', S.source)
    target = ctx.define('target', S.target)
    eq = ctx.mor('eq', p(source, target))
    _, _unique_hat = ctx.mor('unique', prim.unique, (
        req(
            prod(('d', Eq), ('e', Eq)),
            (c(eq, proj('d')), c(eq, proj('e'))),
        ), Eq,
        i, p(('d', i), ('e', i)),
    ))
    _unique_hat(prim.unique_hat)

    return ctx
