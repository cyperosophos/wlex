from ..equality import Verifier, Eq
from ..model.lex import Equalizer
from ..trusted import lex
from . import intensionally_validated as iv, validated as v, ValidationError

class ProofError(ValidationError):
    __slots__ = ('eq',)
    eq: Eq[lex.Mor]

    def __init__(self, eq: Eq[lex.Mor]):
        super().__init__("Missing proof")
        self.eq = eq

def is_parallel(par: lex.Parallel):
    # Unpacking would incur unnecessary steps.
    par.is_valid()

def is_fork(f: lex.Fork, proofs: Verifier[object]):
    # (?) Equalizer fork inherits equality from parallel.
    # Under the limit definition this is an arrow inheriting equality from
    # a functor. Equality of functors can only be extensional.
    # The conclusion here is then that a functor cannot be defined using a limit,
    # since this would force it to inherit equality from morphisms, which would make
    # its equality extensional. The object mapping of a functor can still be built as a limit.

    # Tacit equalities in the limit of the fork.
    is_parallel(f.par)
    # That the handle is already composable with the parallel is
    # given by the initialization.

    # That `e` is intensionally equal to a registered equality is the same as `e` being registered up to transitivity.
    e = f.eq()
    if e not in proofs:
        raise ProofError(e)

def is_lift(l: lex.Lift):
    # TODO: Checking that the lift here actually corresponds to a fork seems
    # superfluous. Cf. pairing and span. The reason is that for a general lift
    # this is already guarantied the target, so there is no point in having a
    # special case where the supermorphism has to be checked.
    # The conclusion is then that the init of Lift and Pairing can't fully be
    # trusted in a public interface. Trusted init would require Fork/Span as args.
    # Does this apply to any other class? This seems to mainly affect Mor subclasses.
    if isinstance(l.target, Equalizer):
        return

    raise ValidationError("Target must be equalizer")

parallel_i = v(lex.parallel_i, is_parallel)
parallel_j = v(lex.parallel_j, is_parallel)
eq_parallel_source = v(lex.eq_parallel_source, is_parallel)
eq_parallel_target = v(lex.eq_parallel_target, is_parallel)
equalizer = v(lex.equalizer, is_parallel)
equalizer_hat = v(lex.equalizer_hat, is_parallel)
lift = iv(lex.lift, is_fork)
lift_hat = iv(lex.lift_hat, is_fork)
lift_ihat = v(lex.lift_ihat, is_lift)
