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

@dataclass(frozen=True)
class BasicQuiverStub:
    Node: _o[Obj]
    Edge: _o[Obj]

    source: _o[MorStub]
    target: _o[MorStub]

@dataclass(frozen=True)
class BasicQuiverTheory(Theory):
    Node: Obj
    Edge: Obj

    source: Mor
    target: Mor

    @classmethod
    def from_ctx(cls, ctx: Context[Self]):
        return cls(
            Node=ctx.obj_refs['Node'],
            Edge=ctx.obj_refs['Edge'],
            source=ctx.mor_refs['source'],
            target=ctx.mor_refs['target'],
        )

    # TODO: define this as an abstract method of Theory!
    def stub_update(self, stub: BasicQuiverStub):
        stub.Node.value = self.Node
        stub.Edge.value = self.Edge
        stub.source.value = self.source
        stub.target.value = self.target

@dataclass(frozen=True)
class QuiverStub:
    Q0: _s[BasicQuiverStub]
    Q1: _s[BasicQuiverStub]

    source_globular_cond: _o[EqStub]
    target_globular_cond: _o[EqStub]

@dataclass(frozen=True)
class QuiverTheory(Theory):
    Q0: BasicQuiverTheory
    Q1: BasicQuiverTheory

    @classmethod
    def from_ctx(cls, ctx: Context[Self]):
        return cls(
            Q0=_ot(ctx.sub_refs['Q0'], BasicQuiverTheory),
            Q1=_ot(ctx.sub_refs['Q1'], BasicQuiverTheory),
        )

def BasicQuiver(stub: _u[BasicQuiverStub]):
    ctx = Context(BasicQuiverTheory)
    prim = _o.prim(stub)

    Node = ctx.obj('Node', prim.Node)
    Edge = ctx.obj('Edge', prim.Edge)

    _ = ctx.mor('source', prim.source, (Edge, Node))
    _ = ctx.mor('target', prim.target, (Edge, Node))

    return ctx

def Quiver(stub: _u[QuiverStub]):
    ctx = Context(QuiverTheory)
    prim = _o.prim(stub)
    c = ctx.c

    Q0 = ctx.sub('Q0', BasicQuiver(prim.Q0))

    def Q1_update(stub: BasicQuiverStub):
        stub.Node.value = Q0.Edge

    Q1 = ctx.sub('Q1', BasicQuiver((prim.Q1, Q1_update)))

    ctx.eq(
        prim.source_globular_cond,
        (
            c(Q0.source, Q1.source),
            c(Q0.source, Q1.target),
        ),
    )

    ctx.eq(
        prim.target_globular_cond,
        (
            c(Q0.target, Q1.source),
            c(Q0.target, Q1.target),
        ),
    )

    return ctx
