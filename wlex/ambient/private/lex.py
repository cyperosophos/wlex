"""Private model of model of `lex` morphisms"""
from ..cells import Mor, Eq
from . import category
from .category import source, target

Parallel = tuple[Mor, Mor]
Fork = tuple[Mor, Mor, Mor, Eq]
EqualizerMor = tuple[Mor, Mor, Mor, Mor, Eq, Eq]

def is_parallel(par: Parallel):
    """Models requirement of `lex.Parallel"""
    i, j = par
    return (
        source(i).identical(source(j))
        and target(i).identical(target(j))
    )

def is_fork(fork: Fork):
    """Models requirement of `lex.Fork`"""
    mor, i, j, eq = fork
    eq_s, eq_t = category.eq_signature(eq)
    return (
        is_parallel((i, j))
        and source(i).identical(target(mor))
        and category.compose((i, mor)).same(eq_s)
        and category.compose((j, mor)).same(eq_t)
    )

def _meqp(par: Parallel):
    mor, _, _, _ = equalizer(par)
    return mor

def is_equalizer_mor(em: EqualizerMor):
    mor, fmor, i, j, feq, eq = em
    eq_s, eq_t = category.eq_signature(eq)
    return (
        is_fork((fmor, i, j, feq))
        and source(mor).identical(source(fmor))
        and target(mor).identical(source(_meqp((i, j))))
        and category.compose((_meqp((i, j)), mor)).same(eq_s)
        and fmor.same(eq_t)
    )

def equalizer(par: Parallel) -> Fork:
    # Using Eq for parallel is possible because globular conditions are public
    # equalities.
    i, j = par
    mor = Eq(i, j).equalizer()
    eq = mor.source.fork(i, j)
    return mor, i, j, eq

# TODO: equalizer_hat

def equalizer_pairing(fork: Fork) -> EqualizerMor:
    mor, i, j, eq = fork
    em = Eq(i, j).equalizer_pairing(mor)
    return em, mor, i, j, eq, mor.ref()

# TODO: equalizer_pairing_hat

def equalizer_pairing_unique(em: EqualizerMor) -> Eq:
    mor, fmor, i, j, _, _ = em
    return Eq(i, j).equalizer_pairing_unique(mor, fmor)

# TODO: equalizer_pairing_unique_hat