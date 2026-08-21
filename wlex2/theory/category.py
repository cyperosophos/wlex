# pylint: disable=C0103, R0902, C0115, C0114
from ..context import Context
from ..variadic.category import compose as c
from ..variadic.lex import pairing as p
from ..element.category import (
    TheoryObj, TheoryMor, TheorySource, TheoryTarget, TheoryIdentity,
)

def category(ctx: Context):
    Obj = ctx.obj('Obj', TheoryObj())
    Mor = ctx.obj('Mor', TheoryMor())

    source_sign = (Mor, Obj)
    source = ctx.mor('source', *source_sign, TheorySource(*source_sign))

    target_sign = (Mor, Obj)
    target = ctx.mor('target', *target_sign, TheoryTarget(*target_sign))

    identity_sign = (Obj, Mor)
    identity = ctx.mor('identity', *identity_sign, TheoryIdentity(*identity_sign))
    ctx.eq()