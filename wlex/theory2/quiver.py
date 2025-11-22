# pylint: disable=C0103
from dataclasses import dataclass
from typing import Self

from wlex.ambient.category import Obj, Mor, Eq, Context, one, Theory, composer

@dataclass
class BasicQuiver(Theory):
    Node: Obj | None = None
    Edge: Obj | None = None

    source: Mor | None = None
    target: Mor | None = None

    #hat: dict
    def with_base(self, base: Self):
        return type(self)(
            Node=one(self.Node, base.Node),
            Edge=one(self.Edge, base.Edge),
            source=one(self.source, base.source),
            target=one(self.target, base.target),
        )

    @classmethod
    def from_prim(cls, ctx: Context, prim: Self):
        Node = ctx.obj('Node', prim.Node)
        Edge = ctx.obj('Edge', prim.Edge)

        source = ctx.mor('source', prim.source, (Edge, Node))
        target = ctx.mor('target', prim.target, (Edge, Node))

        return cls(
            Node=one(Node, prim.Node),
            Edge=one(Edge, prim.Edge),
            source=one(source, prim.source),
            target=one(target, prim.target),
        )

@dataclass
class Quiver(Theory):
    Q0: BasicQuiver | None = None
    Q1: BasicQuiver | None = None

    source_globular_cond: Eq | None = None
    target_globular_cond: Eq | None = None

    def with_base(self, base: Self):
        return type(self)(
            Q0=one(self.Q0, base.Q0),
            Q1=one(self.Q1, base.Q1),
            source_globular_cond=one(
                self.source_globular_cond, base.source_globular_cond,
            ),
            target_globular_cond=one(
                self.target_globular_cond, base.target_globular_cond,
            ),
        )

    @classmethod
    def from_prim(cls, ctx: Context, prim: Self):
        c = composer(ctx)
        Q0 = ctx.sub('Q0', BasicQuiver, prim.Q0)
        Q1 = ctx.sub('Q1', BasicQuiver, prim.Q1, BasicQuiver(
            Node=Q0.Edge,
        ))

        source_globular_cond = ctx.eq(
            'source_globular_cond', prim.source_globular_cond,
            (
                c(Q0.source, Q1.source),
                c(Q0.source, Q1.target),
            ),
        )

        target_globular_cond = ctx.eq(
            'target_globular_cond', prim.target_globular_cond,
            (
                c(Q0.target, Q1.source),
                c(Q0.target, Q1.target),
            ),
        )

        return cls(
            Q0=one(Q0, prim.Q0),
            Q1=one(Q1, prim.Q1),
            source_globular_cond=one(
                source_globular_cond, prim.source_globular_cond,
            ),
            target_globular_cond=one(
                target_globular_cond, prim.target_globular_cond,
            ),
        )
