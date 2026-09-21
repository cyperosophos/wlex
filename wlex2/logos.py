from .model.category import Obj, Mor, Composition
from .model import cart
from .model import lex
from .proven.category import compose
from .proven.cart import terminal_mor, terminal, product, pairing
from .equality import Verifier

class Logos:
    # This can be a singleton
    __slots__ = (
        'null_param', 'params', 'parallels',
        'memo_compose',
        'memo_terminal_mor', 'memo_pairing',
    )
    null_param: cart.NullParam
    params: dict[tuple[Obj, Obj, str], cart.Param]

    # This is of more limited usefulness.
    # We can't always use `Mor` in the key since its __hash__ method would introduce quadratic time
    # (for example during variadic composition).
    # TODO: In variadic equalizer sort the requirements before filling missing requirements,
    # this should guaranty always having the same order.
    parallels: dict[tuple[Obj, Mor, Mor], lex.Parallel]

    # Do memoization with morphisms as well. This means there should be
    # compose, terminal_mor, pairing, lift methods, etc.
    # It makes sense for memoization of (co)limits to be handled at initialization
    # since it is "mandatory."

    memo_compose: dict[tuple[int, int], Mor]
    memo_terminal_mor: dict[Obj, Mor]
    memo_pairing: dict[tuple[int, int, cart.Param], Mor] #?

    # TODO: At some point one needs to provide the (co)limit isomorphisms
    # for proving equalities.

    def __init__(self):
        self.null_param = cart.NullParam()
        #self.null_coparam = NullCoparam() # Place this in a subclass

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

    def _parallel(self, obj: Obj, i: Mor, j: Mor):
        res = self.parallels.get((obj, i, j))
        if res is None:
            res = lex.Parallel(obj, i, j)
            self.parallels[(obj, i, j)] = res

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

        # TODO: Use self.compose, self.lift, self.equalizer.
        i, j = (
            Composition.strict(mor, lex.Lift.strict((
                self.pull_to_product(mor.source, proj.source, idx).restrict(proj),
                mor.source,
            )))
            for mor in obj.par.requirement()
        )
        return lex.Equalizer(self._parallel(prod, i, j))

    def pull_to_equalizer(self, obj: Obj, eqr: Obj, proofs: Verifier[Mor]) -> Obj:
        # `eqr` needs in fact not be an equalizer.
        if obj == eqr.univ:
            return eqr

        if not isinstance(obj, lex.Equalizer):
            raise ValueError("`obj` must be (an equalizer) of the univ.")

        eqr = self.pull_to_equalizer(obj.par.source, eqr, proofs)
        # TODO: Use self.equalizer which should skip tautological requirements!!
        return lex.Equalizer(self._parallel(eqr, *obj.par.requirement()))

    def pairing(self, p: Mor, q: Mor, par: cart.Param):
        span = (id(p), id(q), par)
        res = self.memo_pairing.get(span)
        if res is None:
            res = pairing(cart.Span(p, q, par))
            self.memo_pairing[span] = res

        return res


