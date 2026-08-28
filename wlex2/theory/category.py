# pylint: disable=C0103, R0902, C0115, C0114
from ..context import Context
from ..variadic.lex import limit
from ..element.category import (
    TheoryObj, TheoryMor, TheorySource, TheoryTarget, TheoryIdentity,
    TheoryCompose,
)

def category(ctx: Context):
    c = ctx.compose
    Obj = ctx.obj('Obj', TheoryObj())
    Mor = ctx.obj('Mor', TheoryMor())

    _source_sign = (Mor, Obj)
    source = ctx.mor('source', *_source_sign, TheorySource(*_source_sign))

    _target_sign = (Mor, Obj)
    target = ctx.mor('target', *_target_sign, TheoryTarget(*_target_sign))

    _identity_sign = (Obj, Mor)
    identity = ctx.mor('identity', *_identity_sign, TheoryIdentity(*_identity_sign))
    _identity_hat_sign = (
        c(('', ''), Obj),
        c((source, target), identity),
    )
    ctx.eq(*_identity_hat_sign, ctx.axiom(*_identity_hat_sign))

    Composable = ctx.obj('Composable', limit((
        ('f', Mor),
        ('g', Mor),
    ), (
        c(source, 'f'),
        c(target, 'g'),
    )))

    _compose_sign = (Composable, Mor)
    compose = ctx.mor('compose', *_compose_sign, TheoryCompose(*_compose_sign))
    _compose_hat_sign = (
        c((c(source, 'g'), c(target, 'f')), Composable),
        c((source, target), compose),
    )
    ctx.eq(*_compose_hat_sign, ctx.axiom(*_compose_hat_sign))

    _left_identity_law_sign = (
        c(compose, (c(identity, target), '')),
        '',
    )
    ctx.eq(*_left_identity_law_sign, ctx.axiom(*_left_identity_law_sign))

    _right_identity_law_sign = (
        c(compose, ('', c(identity, source))),
        '',
    )
    ctx.eq(*_right_identity_law_sign, ctx.axiom(*_right_identity_law_sign))

    _associativity_sign = (
        c(compose, ('f', c(compose, ('g', 'h')))),
        c(c(compose, (c(compose, ('f','g')), 'h')), limit((
            ('f', Mor),
            ('g', Mor),
            ('h', Mor),
        ), (
            c(source, 'f'),
            c(target, 'g'),
        ), (
            c(source, 'g'),
            c(target, 'h'),
        ))),
    )
    ctx.eq(*_associativity_sign, ctx.axiom(*_associativity_sign))
