# pylint: disable=C0103
from dataclasses import dataclass
from typing import Self

from wlex.ambient.category import Obj, Mor, Eq, Context, one, Theory, composer
from .quiver import BasicQuiver

@dataclass
class Posetoid(Theory):
    @dataclass
    class _Hat:
        ref: Mor | None = None
        trans: Mor | None = None

    hat: _Hat
    q_: BasicQuiver | None = None
    el_: Obj | None = None
    rel_: Obj | None = None
    source: Mor | None = None
    target: Mor | None = None
    path_: Obj | None = None
    ref: Mor | None = None
    trans: Mor | None = None

    def with_base(self, base: Self):
        return type(self)(
            q_=one(self.q_, base.q_),
            el_=one(self.el_, base.el_),
            rel_=one(self.rel_, base.rel_),
            source=one(self.source, base.source),
            target=one(self.target, base.target),
            path_=one(self.path_, base.path_),
            ref=one(self.ref, base.ref),
            trans=one(self.trans, base.trans),
            hat=self._Hat(
                ref=one(self.hat.ref, base.hat.ref),
                trans=one(self.hat.trans, base.hat.trans),
            )
        )

    @classmethod
    def from_prim(cls, ctx: Context, prim: Self):
        c = composer(ctx)
