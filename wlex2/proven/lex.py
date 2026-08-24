from ..equality import Verifier, Eq
from ..trusted import lex
from . import intensionally_validated as iv, validated as v, ValidationError
from .cart import *

class ProofError(ValidationError):
    __slots__ = ('eq',)
    eq: Eq[lex.Mor]

    def __init__(self, eq: Eq[lex.Mor]):
        super().__init__("Missing proof")
        self.eq = eq

def is_parallel(par: lex.Parallel):
    # Unpacking would incur unnecessary steps.
    # More checks?
    par.is_valid()

    if len(par) == 1:
        raise ValidationError("Invalid parallel")

def is_fork(f: lex.Fork, proofs: Verifier[object]):
    # (?) Equalizer fork inherits equality from parallel.
    # Under the limit definition this is an arrow inheriting equality from
    # a functor. Equality of functors can only be extensional.
    # The conclusion here is then that a functor cannot be defined using a limit,
    # since this would force it to inherit equality from morphisms, which would make
    # its equality extensional. The object mapping of a functor can still be built as a limit.

    # Tacit equalities in the limit of the fork.
    par = f.parallel()
    is_parallel(par)
    ((i, j),) = f.parallel()
    h = f.handle()
    is_composable((i, h))
    is_composable((j, h))

    # That `e` is intensionally equal to a registered equality is the same as `e` being registered up to transitivity.
    (e,) = f.eq()
    if e not in proofs:
        raise ProofError(e)

def is_lift(l: lex.Lift):
    if len(l) != 1:
        raise ValidationError("Lift must have length 1")

    # This check is superfluous, cf. is_pairing
    # mor = l.mor
    # par = l.parallel()
    # eqr = equalizer(par)
    # assert isinstance(eqr, lex.Obj)
    # return target(mor) == eqr

parallel_i = v(lex.parallel_i, is_parallel)
parallel_j = v(lex.parallel_j, is_parallel)
eq_parallel_source = v(lex.eq_parallel_source, is_parallel)
eq_parallel_target = v(lex.eq_parallel_target, is_parallel)
equalizer = v(lex.equalizer, is_parallel)
equalizer_hat = v(lex.equalizer_hat, is_parallel)
lift = iv(lex.lift, is_fork)
lift_hat = iv(lex.lift_hat, is_fork)
lift_ihat = v(lex.lift_ihat, is_lift)
