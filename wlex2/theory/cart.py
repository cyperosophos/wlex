# pylint: disable=C0103, R0902, C0115, C0114
from ..context import Context
from ..variadic.lex import limit
from ..element.cart import (
    TheoryTerminal, TheoryTerminalMorIso, TheoryParam,
    TheoryParamX, TheoryParamY, TheoryProduct, TheoryPairingIso,
)

def cart(ctx: Context):
    c = ctx.compose
    Obj = ctx.obj('Obj')
    Mor = ctx.obj('Mor')
    source = ctx.mor('source')
    target = ctx.mor('target')
    compose = ctx.mor('compose')

    _terminal_sign = (limit(()), Obj)
    terminal = ctx.mor('terminal', *_terminal_sign, TheoryTerminal(*_terminal_sign))

    TerminalMor = ctx.obj('TerminalMor', limit(Mor, (
        target, c(terminal, ()),
    )))

    _terminal_mor_sign = (Obj, TerminalMor)
    terminal_mor = ctx.mor('terminal_mor', *_terminal_mor_sign, TheoryTerminalMorIso(*_terminal_mor_sign))
    _terminal_mor_hat_sign = (Obj, c(source, terminal_mor))
    ctx.eq(*_terminal_mor_hat_sign, ctx.axiom(*_terminal_mor_hat_sign))
    _terminal_mor_ihat_sign = (TerminalMor, c(terminal_mor, source))
    ctx.eq(*_terminal_mor_ihat_sign, ctx.axiom(*_terminal_mor_ihat_sign))

    Param = ctx.obj('Param', TheoryParam())
    _param_x_sign = (Param, Obj)
    param_x = ctx.mor('param_x', *_param_x_sign, TheoryParamX(*_param_x_sign))
    _param_y_sign = (Param, Obj)
    param_y = ctx.mor('param_y', *_param_y_sign, TheoryParamY(*_param_y_sign))

    Span = ctx.obj('Span', limit((
        ('p', Mor),
        ('q', Mor),
        ('par', Param),
    ), (
        c(source, 'p'),
        c(source, 'q'),
    ), (
        param_x,
        c(target, 'p'),
    ), (
        param_y,
        c(target, 'q'),
    )))

    _product_sign = (Param, Span)
    product = ctx.mor('product', *_product_sign, TheoryProduct(*_product_sign))
    _product_hat_sign = (Param, c('par', product))
    ctx.eq(*_product_hat_sign, ctx.axiom(*_product_hat_sign))

    Pairing = ctx.obj('Pairing', limit((
        ('mor', Mor),
        ('par', Param),
    ), (
        c(target, 'mor'),
        c(source, 'p', product, 'par'),
    )))

    _pairing_sign = (Span, Pairing)
    pairing = ctx.mor('pairing', *_pairing_sign, TheoryPairingIso(*_pairing_sign))
    _span = c((
        ('p', c(compose, (c('p', product), 'mor'))),
        ('q', c(compose, (c('q', product), 'mor'))),
        ('par', 'par'),
    ))
    _pairing_hat_sign = (Span, c(_span, pairing))
    ctx.eq(*_pairing_hat_sign, ctx.axiom(*_pairing_hat_sign))
    _pairing_ihat_sign = (Pairing, c(pairing, _span))
    ctx.eq(*_pairing_ihat_sign, ctx.axiom(*_pairing_ihat_sign))
