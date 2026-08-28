# pylint: disable=C0103, R0902, C0115, C0114
from ..context import Context
from ..variadic.lex import limit
from ..element.lex import (
    TheoryEqualizer, TheoryParallel, TheoryParallelI, TheoryParallelJ,
    TheoryLiftIso,
)

def lex(ctx: Context):
    c = ctx.compose
    Mor = ctx.obj('Mor')
    source = ctx.mor('source')
    target = ctx.mor('target')
    compose = ctx.mor('compose')

    Parallel = ctx.obj('Parallel', TheoryParallel())
    _parallel_i_sign = (Parallel, Mor)
    parallel_i = ctx.mor('parallel_i', *_parallel_i_sign, TheoryParallelI(*_parallel_i_sign))
    _parallel_j_sign = (Parallel, Mor)
    parallel_j = ctx.mor('parallel_j', *_parallel_j_sign, TheoryParallelJ(*_parallel_j_sign))

    Fork = ctx.obj('Fork', limit((
        ('mor', Mor),
        ('par', Parallel),
    ), (
        c(compose, (c(parallel_i, 'par'), 'mor')),
        c(compose, (c(parallel_j, 'par'), 'mor')),
    )))

    _equalizer_sign = (Parallel, Fork)
    equalizer = ctx.mor('equalizer', *_equalizer_sign, TheoryEqualizer(*_equalizer_sign))
    _equalizer_sign_hat = (Parallel, c('par', equalizer))
    ctx.eq(*_equalizer_sign, ctx.axiom(*_equalizer_sign))

    Lift = ctx.obj('Lift', limit((
        ('mor', Mor),
        ('par', Parallel),
    ), (
        c(target, 'mor'),
        c(source, 'mor', equalizer, 'par'),
    )))

    _lift_sign = (Fork, Lift)
    lift = ctx.mor('lift', *_lift_sign, TheoryLiftIso(*_lift_sign))
    _fork = c((
        ('mor', c(compose, (c('mor', equalizer), 'mor'))),
        ('par', 'par'),
    ))
    _lift_hat_sign = (Fork, c(_fork, lift))
    ctx.eq(*_lift_hat_sign, ctx.axiom(*_lift_hat_sign))
    _lift_ihat_sign = (Lift, c(lift, _fork))
    ctx.eq(*_lift_ihat_sign, ctx.axiom(*_lift_ihat_sign))
