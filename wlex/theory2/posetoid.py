# pylint: disable=C0103, R0902, R0914, C0115, C0114
from dataclasses import dataclass
from typing import Self

from wlex.ambient.category import (
    Obj, Mor, Eq as MetaEq, Theory, TheoryStub,
    MorStub, EqStub,
)
from wlex.ambient.category import one as _
from wlex.ambient.lex import LexContext#, requirer
from .quiver import BasicQuiver, BasicQuiverStub

@dataclass
class PosetoidStub(TheoryStub):
    Q: BasicQuiverStub | None = None
    ref: MorStub | None = None
    trans: MorStub | None = None
    ref_hat: EqStub | None = None
    trans_hat: EqStub | None = None

    def with_base(self, base: Self):
        return type(self)(
            Q=_(self.Q, base.Q),
            ref=_(self.ref, base.ref),
            trans=_(self.trans, base.trans),
            ref_hat=_(self.ref_hat, base.ref_hat),
            trans_hat=_(self.trans_hat, base.trans_hat),
        )

    @classmethod
    def from_theory(cls, theory: 'Posetoid') -> Self:
        return cls(
            Q=BasicQuiverStub.from_theory(theory.Q),
            ref=theory.ref,
            trans=theory.trans,
            ref_hat=theory.ref_hat,
            trans_hat=theory.trans_hat,
        )

@dataclass
class Posetoid(Theory):
    Q: BasicQuiver
    El: Obj
    Rel: Obj
    source: Mor
    target: Mor
    Path: Obj
    ref: Mor
    trans: Mor
    ref_hat: MetaEq
    trans_hat: MetaEq

    @classmethod
    def from_prim(cls, ctx: LexContext, prim: PosetoidStub):
        c = ctx.c
        p = ctx.pair0
        prod = ctx.prod
        #require = requirer(ctx)
        proj = ctx.proj
        i = ctx.id

        Q = ctx.sub('Q', BasicQuiver, _(prim.Q))
        El = Q.Node
        Rel = Q.Edge
        source = Q.source
        target = Q.target

        Path = require(
            prod(('f', Rel), ('g', Rel)),
            ('', c(source, proj('f')), c(target, proj('g'))),
        )

        ref, _ref_hat = ctx.mor('ref', _(prim.ref), (
            c(p(('', i), ('', i)), El),
            p(('', source), ('', target)),
        ))
        ref_hat = _ref_hat(_(prim.ref_hat))
        trans, _trans_hat = ctx.mor('trans', _(prim.trans), (
            c(p(
                ('', c(source, proj('g'))),
                ('', c(target, proj('f'))),
            ), Path),
            p(('', source), ('', target)),
        ))
        trans_hat = _trans_hat(_(prim.trans_hat))

        return cls(
            Q=Q,
            El=El,
            Rel=Rel,
            source=source,
            target=target,
            Path=Path,
            ref=ref,
            trans=trans,
            ref_hat=ref_hat,
            trans_hat=trans_hat,
        )

@dataclass
class SetoidStub(TheoryStub):
    P: PosetoidStub | None = None
    sym: MorStub | None = None
    sym_hat: EqStub | None = None

    def with_base(self, base: Self):
        return type(self)(
            P=_(self.P, base.P),
            sym=_(self.sym, base.sym),
            sym_hat=_(self.sym_hat, base.sym_hat),
        )

    @classmethod
    def from_theory(cls, theory: 'Setoid') -> Self:
        return cls(
            P=PosetoidStub.from_theory(theory.P),
            sym=theory.sym,
            sym_hat=theory.sym_hat,
        )

@dataclass
class Setoid(Theory):
    P: Posetoid
    Eq: Obj
    source: Mor
    target: Mor
    sym: Mor
    sym_hat: MetaEq

    @classmethod
    def from_prim(cls, ctx: Context, prim: SetoidStub) -> Self:
        p = pairer0(ctx)

        P = ctx.sub('P', Posetoid, _(prim.P))
        Eq = P.Rel
        source = P.source
        target = P.target
        sym, _sym_hat = ctx.mor('sym', _(prim.sym), (
            p(('', source), ('', target)),
            p(('', target), ('', source)),
        ))
        sym_hat = _sym_hat(_(prim.sym_hat))

        return cls(
            P=P,
            Eq=Eq,
            source=source,
            target=target,
            sym=sym,
            sym_hat=sym_hat,
        )

@dataclass
class CongruenceStub(TheoryStub):
    S: SetoidStub | None = None
    unique: MorStub | None = None
    unique_hat: EqStub | None = None

    def with_base(self, base: Self):
        return type(self)(
            S=_(self.S, base.S),
            unique=_(self.unique, base.unique),
            unique_hat=_(self.unique_hat, base.unique_hat)
        )

    @classmethod
    def from_theory(cls, theory: 'Congruence') -> Self:
        return cls(
            S=SetoidStub.from_theory(theory.S),
            unique=theory.unique,
            unique_hat=theory.unique_hat,
        )

@dataclass
class Congruence(Theory):
    S: Setoid
    Eq: Obj
    source: Mor
    target: Mor
    eq: Mor
    unique: Mor
    unique_hat: MetaEq

    @classmethod
    def from_prim(cls, ctx: Context, prim: CongruenceStub) -> Self:
        c = composer(ctx)
        p = pairer0(ctx)
        product = producer(ctx)
        require = requirer(ctx)
        proj = ctx.proj
        i = ctx.id

        S = ctx.sub('S', Setoid, _(prim.S))
        Eq = S.Eq
        source = S.source
        target = S.target
        eq = ctx.mor('eq', p(('', source), ('', target)))
        unique, _unique_hat = ctx.mor('unique', _(prim.unique), (
            require(
                product(('d', Eq), ('e', Eq)),
                ('', c(eq, proj('d')), c(eq, proj('e'))),
            ),
            c(p(('', i), ('', i)), Eq),
        ))
        unique_hat = _unique_hat(_(prim.unique_hat))

        return cls(
            S=S,
            Eq=Eq,
            source=source,
            target=target,
            eq=eq,
            unique=unique,
            unique_hat=unique_hat,
        )
