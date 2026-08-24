# pylint: disable=C0103, R0902, C0115, C0114
from ..context import Context
from ..variadic.category import adapting_compose as c
from ..variadic.cart import adapting_pairing as p, prod, proj
from ..variadic.lex import req
from ..element.category import (
    TheoryObj, TheoryMor, TheorySource, TheoryTarget, TheoryIdentity,
    TheoryCompose,
)
from ..proven.category import identity as idty

def category(ctx: Context):
    Obj = ctx.obj('Obj', TheoryObj())
    Mor = ctx.obj('Mor', TheoryMor())

    _source_sign = (Mor, Obj)
    source = ctx.mor('source', *_source_sign, TheorySource(*_source_sign))

    _target_sign = (Mor, Obj)
    target = ctx.mor('target', *_target_sign, TheoryTarget(*_target_sign))

    _identity_sign = (Obj, Mor)
    identity = ctx.mor('identity', *_identity_sign, TheoryIdentity(*_identity_sign))
    _identity_hat_sign = (
        c(p(idty, idty), Obj),
        c(p(source, target), identity),
    )
    ctx.eq(*_identity_hat_sign, ctx.axiom(*_identity_hat_sign))

    Composable = ctx.obj('Composable', req(prod(
        ('f', Mor),
        ('g', Mor),
    ), (
        c(source, proj('f')),
        c(target, proj('g')),
    )))

    _compose_sign = (Composable, Mor)
    compose = ctx.mor('compose', *_compose_sign, TheoryCompose(*_compose_sign))
    _compose_hat_sign = (
        c(p(c(source, proj('g')), c(target, proj('f'))), Composable),
        c(p(source, target), compose),
    )
    ctx.eq(*_compose_hat_sign, ctx.axiom(*_compose_hat_sign))

    _left_identity_law_sign = (
        c(compose, p(c(identity, target), idty)),
        idty,
    )
    ctx.eq(*_left_identity_law_sign, ctx.axiom(*_left_identity_law_sign))

    _right_identity_law_sign = (
        c(compose, p(idty, c(identity, source))),
        idty,
    )
    ctx.eq(*_right_identity_law_sign, ctx.axiom(*_right_identity_law_sign))

    _associativity_sign = (
        c(compose, p(proj('f'), c(compose, p(proj('g'), proj('h'))))),
        c(c(compose, p(c(compose, p(proj('f'), proj('g'))), proj('h'))), req(prod(
            ('f', Mor),
            ('g', Mor),
            ('h', Mor),
        ), (
            c(source, proj('f')),
            c(target, proj('g')),
        ), (
            c(source, proj('g')),
            c(target, proj('h')),
        ))),
    )
    ctx.eq(*_associativity_sign, ctx.axiom(*_associativity_sign))
