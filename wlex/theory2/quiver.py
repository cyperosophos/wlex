# pylint: disable=C0103, R0902, C0115, C0114
from dataclasses import dataclass
from typing import Self

from wlex.ambient.category import (
    Obj, Mor, Eq, Context, Theory, TheoryStub,
    MorStub, EqStub,
)
from wlex.ambient.category import one as _

@dataclass
class BasicQuiverStub(TheoryStub):
    # Includes only the primitives
    Node: Obj | None = None
    Edge: Obj | None = None

    source: MorStub | None = None
    target: MorStub | None = None

    def with_base(self, base: Self):
        return type(self)(
            Node=_(self.Node, base.Node),
            Edge=_(self.Edge, base.Edge),
            source=_(self.source, base.source),
            target=_(self.target, base.target),
        )

    @classmethod
    def from_theory(cls, theory: 'BasicQuiver') -> Self:
        return cls(
            Node=theory.Node,
            Edge=theory.Edge,
            source=theory.source,
            target=theory.target,
        )

@dataclass
class BasicQuiver(Theory):
    Node: Obj
    Edge: Obj

    source: Mor
    target: Mor

    Stub = BasicQuiverStub

    @classmethod
    def from_prim(cls, ctx: Context, prim: BasicQuiverStub):
        Node = ctx.obj('Node', _(prim.Node))
        Edge = ctx.obj('Edge', _(prim.Edge))

        source = ctx.mor('source', _(prim.source), (Edge, Node))
        target = ctx.mor('target', _(prim.target), (Edge, Node))

        return cls(
            Node=Node,
            Edge=Edge,
            source=source,
            target=target,
        )

@dataclass
class QuiverStub(TheoryStub):
    Q0: BasicQuiverStub | None = None
    Q1: BasicQuiverStub | None = None

    eqs: tuple[EqStub | None, EqStub | None] = (None, None)

    def with_base(self, base: Self):
        eqs = tuple(_(s, b) for s, b in zip(self.eqs, base.eqs))
        assert len(eqs) == 2
        return type(self)(
            Q0=_(self.Q0, base.Q0),
            Q1=_(self.Q1, base.Q1),
            eqs=eqs,
        )

    @classmethod
    def from_theory(cls, theory: 'Quiver') -> Self:
        return cls(
            Q0=BasicQuiverStub.from_theory(theory.Q0),
            Q1=BasicQuiverStub.from_theory(theory.Q1),
            eqs=theory.eqs,
        )

@dataclass
class Quiver(Theory):
    Q0: BasicQuiver
    Q1: BasicQuiver

    eqs: tuple[Eq, Eq]

    Stub = QuiverStub

    @classmethod
    def from_prim(cls, ctx: Context, prim: QuiverStub):
        c = ctx.c
        Q0 = ctx.sub('Q0', BasicQuiver, _(prim.Q0))
        Q1 = ctx.sub('Q1', BasicQuiver, _(prim.Q1), BasicQuiverStub(
            Node=Q0.Edge,
        ))

        # It the future, naming equalities may become optional.
        source_globular_cond = ctx.eq(
            _(prim.eqs[0]),
            (
                c(Q0.source, Q1.source),
                c(Q0.source, Q1.target),
            ),
        )

        target_globular_cond = ctx.eq(
            _(prim.eqs[1]),
            (
                c(Q0.target, Q1.source),
                c(Q0.target, Q1.target),
            ),
        )

        return cls(
            Q0=Q0,
            Q1=Q1,
            eqs=(source_globular_cond, target_globular_cond),
        )

# TODO: Support referencing eqs by signature, and perhaps some factoring resolution.
# TODO: Full review of ambient/category
# TODO: Full review of ambient/cart (it's not clear that the semantics of labeled params, especially with regards to '', label has been kept.)
# TODO: Named eqs are just morphisms () -> Eq. All morphisms to Eq provide a proof of equalities with a certain signature.
#       Equalities from equalizers are not referred by name, so they are resolved based on signature.
#       All signature resolution is ad hoc and corresponds to morphisms with target Eq.
#       The idea is that in some case the construction is computationally feasible.
#       Running (type checking) the morphisms is just the verification of the construction.
