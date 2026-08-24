# pylint: disable=C0103, R0902, C0115, C0114
from ..context import Context
from ..variadic.category import adapting_compose as c
from ..variadic.cart import adapting_pairing as p, prod, proj
from ..variadic.lex import req
from ..element.cart import (
    TheoryTerminal, TheoryTerminalMorIso, TheoryParam,
    TheoryParamX, TheoryParamY, TheoryProduct, TheoryPairingIso,
)
from ..proven.cart import terminal as t, terminal_mor as tmor

def cart(ctx: Context):
    Obj = ctx.obj('Obj')
    Mor = ctx.obj('Mor')
    target = ctx.mor('target')
    source = ctx.mor('source')
    compose = ctx.mor('compose')

    _terminal_sign = (t(), Obj)
    terminal = ctx.mor('terminal', *_terminal_sign, TheoryTerminal(*_terminal_sign))

    TerminalMor = ctx.obj('TerminalMor', req(Mor, (
        target, c(terminal, tmor(Mor)),
    )))

    _terminal_mor_sign = (Obj, TerminalMor)
    terminal_mor = ctx.mor('terminal_mor', *_terminal_mor_sign, TheoryTerminalMorIso(*_terminal_mor_sign))
    _terminal_mor_hat_sign = (
        Obj,
        c(source, terminal_mor), # TODO: Requires straightening!
    )
