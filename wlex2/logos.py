from weakref import WeakValueDictionary as wdict

from .model.category import Obj, Mor, Composition
from .model import cart
from .model import lex
from .proven.category import compose, identity
from .proven.cart import terminal_mor, terminal, product, pairing
from .proven.lex import equalizer, lift
from .equality import Verifier

class Logos:
    # This can be a singleton
    __slots__ = (
        '_default_proofs',
        'null_param', 'params', 'parallels',
        'memo_identity', 'memo_compose',
        'memo_terminal_mor', 'memo_pairing',
        'memo_lift',
    )
    _default_proofs: Verifier[Mor]
    null_param: cart.NullParam
    params: wdict[tuple[Obj, Obj, str], cart.Param]

    # This is of more limited usefulness.
    # We can't always use `Mor` in the key since its __hash__ method would introduce quadratic time
    # (for example during variadic composition).
    # TODO: In variadic equalizer sort the requirements before filling missing requirements,
    # this should guaranty always having the same order.
    parallels: wdict[tuple[int, int, int], lex.Parallel]

    # Do memoization with morphisms as well. This means there should be
    # compose, terminal_mor, pairing, lift methods, etc.
    # It makes sense for memoization of (co)limits to be handled at initialization
    # since it is "mandatory."

    memo_identity: wdict[Obj, Mor]
    memo_compose: wdict[tuple[int, int], Mor]
    memo_terminal_mor: wdict[Obj, Mor]
    memo_pairing: wdict[tuple[int, int, cart.Param], Mor] #?
    memo_lift: wdict[tuple[int, lex.Parallel], Mor]

    # TODO: At some point one needs to provide the (co)limit isomorphisms
    # for proving equalities.

    def __init__(self):
        self._default_proofs = Verifier(set())
        self.null_param = cart.NullParam()
        #self.null_coparam = NullCoparam() # Place this in a subclass

    def identity(self, obj: Obj) -> Mor:
        res = self.memo_identity.get(obj)
        if res is None:
            res = identity(obj)
            self.memo_identity[obj] = res

        return res

    def compose(self, f: Mor, g: Mor) -> Mor:
        c = (id(f), id(g))
        res = self.memo_compose.get(c)
        if res is None:
            res = compose((f, g))
            self.memo_compose[c] = res

        return res

    def terminal_mor(self, source: Obj) -> Mor:
        res = self.memo_terminal_mor.get(source)
        if res is None:
            res = terminal_mor(cart.NullSpan(source, self.null_param))
            self.memo_terminal_mor[source] = res

        return res

    def terminal(self):
        return terminal(self.null_param)

    def _param(self, x: Obj, y: Obj, label: str):
        res = self.params.get((x, y, label))
        if res is None:
            res = cart.Param(x, y, label)
            self.params[(x, y, label)] = res

        return res

    def product(self, x: Obj, y: Obj, label: str):
        if isinstance(x, cart.Product):
            if label in x.labels:
                raise ValueError('Repeated label')

        if isinstance(x, lex.Equalizer) or isinstance(y, lex.Equalizer):
            raise ValueError("Equalizer objects are not allowed as param")

        return product(self._param(x, y, label))

    def _parallel(self, handle: Mor, i: Mor, j: Mor):
        args = (id(handle), id(i), id(j))
        res = self.parallels.get(args)
        if res is None:
            res = lex.Parallel(handle, i, j)
            self.parallels[args] = res

        return res

    def pull_to_product(self, obj: Obj, prod: Obj, idx: int) -> Obj:
        # Return a product with `obj` as component along with the
        # requirements of `obj`. This means that if `obj` is an
        # equalizer, its (top) superobject has to be a component of `prod`,
        # and then the returned object is an equalizer with appropriate
        # requirements and `prod` as its (top) superobject.
        if obj == prod.component(idx):
            return prod

        if not isinstance(obj, lex.Equalizer):
            raise ValueError("`obj` must be (an equalizer of) a component.")

        # Include all previous requirements
        prod = self.pull_to_product(obj.par.source, prod, idx)
        # This projection gets precomposed (after any restrict-lifting) with
        # each morphism of the parallel pair, so its source is only required
        # to be a superobject of `prod`. Hence, we don't use the proj method,
        # which returns a projection with the equalizer as the source.
        proj = prod.proj(idx).extend()
        #assert isinstance(proj, cart.Projection)

        # TODO: Use self.lift, self.equalizer.
        i, j = (
            self.compose(mor, lex.Lift.strict((
                self.pull_to_product(mor.source, proj.source, idx).restrict(proj),
                mor.source,
            )))
            for mor in obj.par.req()
        )
        # Notice that fp = gp => f = g (with p being a projection) iff
        # the source of p is inhabited, so we let this be handled by self.equalizer
        # to deal with the case of an empty source (fp = gp is then obviously
        # tautological).
        # TODO: The verifier should handle some easy to proof equalities (e.g.
        # those arising from the (co)limit isomorphisms).
        return self.equalizer(prod, i, j)

    def pull_to_equalizer(self, obj: Obj, eqr: Obj, proofs: Verifier[Mor]) -> Obj:
        # `eqr` needs in fact not be an equalizer.
        if obj == eqr.univ:
            return eqr

        if not isinstance(obj, lex.Equalizer):
            raise ValueError("`obj` must be (an equalizer) of the univ.")

        eqr = self.pull_to_equalizer(obj.par.source, eqr, proofs)
        # A previous requirement may become tautological after adding the new requirement.
        return self.equalizer(eqr, *obj.par.req(), proofs)

    def precompose_equalizer(self, mor: Mor, eqr: Obj, proofs: Verifier[Mor]) -> Mor:
        # Notice that this equalizer is not guaranteed to exist by a theorem.
        # It is instead provided as an axiom of the logos.
        # The purpose is to obtain a new source for `mor`, so that it can have `eqr` as its
        # target. This means that the target of `mor` has to be a subobject of `eqr.univ`.
        # The super object check is handled by equalizer type checking of the parallel.
        # For simplicity we reconstruct from univ, i.e. start from the first parallel.
        if isinstance(eqr, lex.Equalizer):
            return self.equalizer(
                self.precompose_equalizer(mor, eqr.par.source, proofs),
                *eqr.par.req(),
                proofs,
            ).restrict(mor)

        return eqr.restrict(mor)

    def pairing(self, p: Mor, q: Mor, par: cart.Param):
        span = (id(p), id(q), par)
        res = self.memo_pairing.get(span)
        if res is None:
            res = pairing(cart.Span(p, q, par))
            self.memo_pairing[span] = res

        return res

    def shrink_fork(self, fork: lex.Fork, proofs: Verifier[Mor]) -> tuple[Mor, lex.Fork | None]:
        handle = fork.mor()
        if isinstance(handle, Composition):
            rest, shrunk = self.shrink_fork(lex.Fork(
                handle.f,
                fork.par,
            ), proofs)
        else:
            rest = None
            shrunk = None

        if shrunk is None:
            i, j = fork.par.eq()
            if (
                self.compose(i, handle),
                self.compose(j, handle),
            ) in proofs:
                return self.identity(handle.source), fork

            return handle, None

        assert rest
        assert isinstance(handle, Composition)
        return self.compose(rest, handle.g), shrunk

    def equalizer(self, obj: Obj | Mor, i: Mor, j: Mor, proofs: Verifier[Mor] | None = None):
        if isinstance(obj, Obj):
            handle = self.identity(obj)
        else:
            handle = obj

        if proofs is None:
            proofs = self._default_proofs

        par = self._parallel(handle, i, j)
        if (
            # The case of equality without handle occurs especially when restricting
            # (for lifting) a morphism whose target already satisfies the requirement.
            self._parallel(self.identity(handle.target), i, j).eq() in proofs
            or par.eq in proofs
        ):
            return handle.source

        return equalizer(par)

    def lift(self, mor: Mor, par: lex.Parallel, proofs: Verifier[Mor]):
        if isinstance(mor, Composition):
            # Try lifting first mor.f so as to shrink the fork. We need this for
            # (deep) lifting when the original target of the handle is too small.
            try:
                i = lift(lex.Fork(mor.f, par), proofs)
            except ...

        fork = (id(mor), par)
        # One stores all forks, not just the most restrictive fork.
        # Usually this will only store at most one extra Fork instance per equality
        # (or equalizer requirement), but sometimes the equality may just be inferred.
        res = self.memo_lift.get(fork)
        if res is None:
            # No fork shrinking here, since this is applied to each factor of the composition.
            res = lift(lex.Fork(mor, par), proofs)
            self.memo_lift[fork] = res

        return res

    def _deep_lift(self, mor: Mor, eqr: Obj, proofs: Verifier[Mor]) -> Mor:
        if isinstance(eqr, lex.Equalizer):
            return self.lift(self._deep_lift(
                mor, eqr.par.source, proofs,
            ), eqr.par, proofs)

        # We call incl to handle requirements already satisfied by mor.target.
        # This is complicated by the fact that we need some way to cancel incl with
        # lifting (e.g. by shrinking the fork). We use the fact that mor.f will be
        # the lowering inclusion.
        # We have to lower mor so that its target coincides with eqr.sup.
        # We can't just use a sufficiently large superset of the original eqr
        # (one that would equal mor.target) because the order of requirements may
        # not be fit for this. Instead of calling incl we could use the following
        # shortcut: skip lifting whenever the requirement is already satisfied
        # by mor.target. However we are still left with the problem of creating
        # a valid fork (by having the target of the handle coincide with the source
        # of the parallel).
        return mor.incl(eqr)

    def fit(self, mor: Mor, target: Obj, proofs: Verifier[Mor]):
        # `mor.target` may hav extra requirements. *This is actually incl-restrict-lift.*
        # This means that all extra requirements get discarded at the beginning
        # by calling incl. We do not discard all requirements since reintroducing
        # common requirements would be wasteful.
        # The alternative is to lift then include (as has already been done
        # in previous versions). This has the advantage that we don't end up
        # with a composition as the morphism being lifted (more simplified).
        # Here we use `pull_to_equalizer` for adding the extra requirements to target.
        # *restrict-lift-incl*
        # TODO: We don't call `pull_to_product` here. Check that weakening
        # is being handled correctly.

        # This is the same as an intersection. We need it to be a subset of mor.target
        # to be able to lift mor, and a subset of target to be able to lower the result.
        subtarget = self.pull_to_equalizer(target, mor.target, proofs)

        # The problem of alternating lifting and restricting is that one ends up
        # with lift with composition within lift *unless one always absorbs the inclusion
        # into the lift*. So it is better to restrict once for all needed requirements.
        # The way it currently works is that one effectively chooses the shortes handle
        # for the fork by lifting each factor left to right of the composition and then
        # reducing so that superfluous inclusions are removed and lifts are merged.
        restricted = self.precompose_equalizer(mor, target, proofs)

        return self._deep_lift(restricted, subtarget, proofs).incl(target)

        # The idea is that one restricts as much as needed here by replacing the
        # "pulled equalizer" for the source of target (restricting). When creating
        # this new equalizer tautological requirements will get discarded (except of
        # course the ones that become tautological because of a later requirement, but
        # this is not an issue, since the verifier would only catch such proof after restricting
        # according to the later requirement).
        # Actually instead of `pull_equalizer`, we create a new equalizer by precomposing
        # all requirements of target with `mor`. This may require lifing and be recursive.
        # Notice that the existence of this equalizer is not guaranteed by the existence of the first equalizer.
        # Resursively modify target.par for creating new equalizer. See `pull_to_*`.
