# pylint: disable=C0103, R0902, C0115, C0114
from dataclasses import dataclass
from typing import Self

from wlex.ambient.category import (
    Obj, Mor, Eq, Context, Theory, TheoryStub, composer,
)
from wlex.ambient.category import one as _

@dataclass
class BasicQuiverStub(TheoryStub):
    # Includes only the primitives
    Node: Obj | None = None
    Edge: Obj | None = None

    source: Mor | None = None
    target: Mor | None = None

    def with_base(self, base: Self):
        return type(self)(
            Node=_(self.Node, base.Node),
            Edge=_(self.Edge, base.Edge),
            source=_(self.source, base.source),
            target=_(self.target, base.target),
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

    source_globular_cond: Eq | None = None
    target_globular_cond: Eq | None = None

    def with_base(self, base: Self):
        return type(self)(
            Q0=_(self.Q0, base.Q0),
            Q1=_(self.Q1, base.Q1),
            source_globular_cond=_(
                self.source_globular_cond, base.source_globular_cond,
            ),
            target_globular_cond=_(
                self.target_globular_cond, base.target_globular_cond,
            ),
        )

@dataclass
class Quiver(Theory):
    Q0: BasicQuiver
    Q1: BasicQuiver

    source_globular_cond: Eq
    target_globular_cond: Eq

    Stub = QuiverStub

    @classmethod
    def from_prim(cls, ctx: Context, prim: QuiverStub):
        c = composer(ctx)
        Q0 = ctx.sub('Q0', BasicQuiver, _(prim.Q0))
        Q1 = ctx.sub('Q1', BasicQuiver, _(prim.Q1), BasicQuiverStub(
            Node=Q0.Edge,
        ))

        source_globular_cond = ctx.eq(
            'source_globular_cond', _(prim.source_globular_cond),
            (
                c(Q0.source, Q1.source),
                c(Q0.source, Q1.target),
            ),
        )

        target_globular_cond = ctx.eq(
            'target_globular_cond', _(prim.target_globular_cond),
            (
                c(Q0.target, Q1.source),
                c(Q0.target, Q1.target),
            ),
        )

        return cls(
            Q0=Q0,
            Q1=Q1,
            source_globular_cond=source_globular_cond,
            target_globular_cond=target_globular_cond,
        )
