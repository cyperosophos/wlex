from dataclasses import dataclass
from typing import Self
from ..ambient.cells import Obj, Mor, Eq
from ..ambient.category import Context, one, Theory

@dataclass
class BasicQuiver(Theory):
    node_: Obj | None = None
    edge_: Obj | None = None

    source: Mor | None = None
    target: Mor | None = None

    #hat: dict
    def with_base(self, base: Self):
        return type(self)(
            node_=one(self.node_, base.node_),
            edge_=one(self.edge_, base.edge_),
            source=one(self.source, base.source),
            target=one(self.target, base.target),
        )

    @classmethod
    def from_prim(cls, ctx: Context, prim: Self):
        node_ = ctx.obj('Node', prim.node_)
        edge_ = ctx.obj('Edge', prim.edge_)

        source = ctx.mor('source', prim.source, (edge_, node_))
        target = ctx.mor('target', prim.target, (edge_, node_))

        return cls(
            node_=one(node_, prim.node_),
            edge_=one(edge_, prim.edge_),
            source=one(source, prim.source),
            target=one(target, prim.target),
        )

@dataclass
class Quiver(Theory):
    q0_: BasicQuiver | None = None
    q1_: BasicQuiver | None = None

    source_globular_cond: Eq | None = None
    target_globular_cond: Eq | None = None

    def with_base(self, base: Self):
        return type(self)(
            q0_=one(self.q0_, base.q0_),
            q1_=one(self.q1_, base.q1_),
            source_globular_cond=one(
                self.source_globular_cond, base.source_globular_cond,
            ),
            target_globular_cond=one(
                self.target_globular_cond, base.target_globular_cond,
            ),
        )

    @classmethod
    def from_prim(cls, ctx: Context, prims: Self):
        q0_ = ctx.sub('Q0', BasicQuiver, prims.q0_)
        q1 = ctx.sub('Q1', BasicQuiver, prims.q1_, BasicQuiver(
            node_ = q0_.edge_,
        ))

        source_globular_cond = ctx.eq(
            'source_globular_cond', prims.source_globular_cond,
            ()
        )


# This should work with just the public ambient interface.
# ctx is for keepring track of names.