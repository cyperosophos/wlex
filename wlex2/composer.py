from typing import Callable, Iterable, Iterator, TypeGuard
from itertools import chain

from .transform import Transform, resolve
from .model.category import Obj, Mor
from .model.cart import Product, Pairing
from .model.lex import Equalizer, Lift
from .proven import category
from .trusted import category as pcategory
from .logos import Logos

LabeledMor = tuple[str, Mor] | Mor
CartMor = Mor | tuple[LabeledMor, ...]
LabeledTransform = tuple[str, Transform] | Transform
CartTransform = Transform | tuple[LabeledTransform, ...]
Composable = Iterable[CartMor]

class Composer:
    # Lex composer
    __slots__ = ('pending', 'factors')
    pending: list[Transform | tuple[LabeledTransform, ...]]
    factors: Iterable[CartTransform]
    logos = Logos()

    def __init__(self, factors: Iterable[CartTransform | Obj]):
        self.pending = []
        self.factors = (
            pcategory.identity(x) if isinstance(x, Obj) else x
            for x in factors
        )

    def flush(self, source: Obj):
        res: list[CartMor] = []
        for factor in reversed(self.pending):
            if isinstance(factor, (Mor, Callable, str, int)):
                mor = resolve(factor, source)
                source = mor.target
            elif factor == ():
                mor = self.logos.terminal_mor(source)
                source = mor.target
            else:
                mor = tuple(
                    _resolve_labeled(f, source)
                    for f in factor
                )
                source = self._tuple_target(mor)

            res.append(mor)

        del self.pending[:]
        return reversed(res)

    def composable(self) -> Iterator[CartMor]:
        pending = self.pending
        for factor in self.factors:
            if factor == ():
                pending.append(factor)
            elif _is_cart_mor(factor):
                if isinstance(factor, tuple):
                    src = self._tuple_target(factor)
                else:
                    src = factor.target

                yield from self.flush(src)
                yield factor
            else:
                pending.append(factor)

    def _fit_factor(self, target: Obj, factor: Mor) -> Mor:
        # This gets called when `target` != `factor.target`
        # TODO: Support coproj for Coproduct
        # Make superobjects coincide
        #if not isinstance(target, Equalizer):
        #    return factor.proj(target)

        # Restrict and lift
        return self.lift(factor, target).incl(target)

    def fit_factor(self, target: Obj, factor: CartMor) -> Mor:
        if isinstance(factor, Mor):
            return self._fit_factor(target, factor.proj(target.univ))

        #if not isinstance(target, Product):
        #    raise ValueError('Target must be product')

        # factor = tuple(
        #     c.incl() if isinstance(c, Mor) else c[1].incl()
        #     for c in factor
        # )

        # target could be an equalizer. In this case lifting is needed.
        # At this point all targets have been determined, for example the target obtained
        # from a tuple may be an equalizer of a product. Hence we lower all morphisms of the
        # tuple so that we obtain a pairing, and then lift as in `_fit_factor`.
        # The target passed to the pairing must be a product. Recall that we don't allow
        # products with equalizer components. Call incl() on each component for lowering it.
        # TODO: variadic equalizer should disallow all tautological reqs
        # not just repeated reqs.
        # No projection with pairing, since there is no point in removing components that
        # are being explicitly stated.
        return self._fit_factor(
            target,
            self.pairing(factor, target.univ),
        )

    def _compose(self, c: Composable):
        it = iter(c)
        for factor in it:
            res = factor
            break
        else:
            assert False

        if isinstance(res, tuple):
            tgt = self._tuple_target(res)
            res = self._fit_factor(
                tgt,
                self.pairing(res, tgt.univ),
            )

        for factor in it:
            res = category.compose((
                res,
                self.fit_factor(res.source, factor)
            ))

        return res

    def _tuple_target(self, factor: tuple[LabeledMor, ...]):
        # This is used when there is no target for passing to `variadic.pairing`.
        res = self.product(
            m.target
            if isinstance(m, Mor)
            else (m[0], m[1].target)
            for m in factor
        )
        return res

    def pairing(
        self, components: Iterable[LabeledMor],
        target: Obj,
    ) -> Pairing:
        # Lower (incl) components here.
        # Check that target is product.

        it = iter(components)
        for first in it:
            break
        else:
            raise ValueError("Empty components")

        # Labeling requires starting from the terminal_mor as the actual
        # unlabeled first component.
        # it = chain((first,), it)
        # The common source is the intersection of all sources.

        raise TypeError("Pairing not supported")

    @classmethod
    def product(cls, components: Iterable[tuple[str, Obj] | Obj]) -> Obj:
        logos = cls.logos
        res = logos.terminal()
        for i, component in enumerate(components):
            if isinstance(component, tuple):
                label, component = component
            else:
                label = ''

            res = logos.product(res, component.univ, label)

        for i, component in enumerate(components):
            if isinstance(component, tuple):
                _, component = component

            # This is a consequence of the Parallel class provided by logos.
            res = logos.pull_to_product(component, res, i)

        return res

    def lift(
        self, mor: Mor,
        target: Obj,
    ) -> Lift:
        raise TypeError("Lift not supported")

    def compose(self) -> Transform:
        factors = self.composable()
        if self.pending:
            def comp(src: Obj):
                return self._compose(chain(
                    factors,
                    self.flush(src),
                ))

            return comp

        return self._compose(factors)

def _is_cart_mor(
    f: CartTransform,
) -> TypeGuard[CartMor]:
    if isinstance(f, Mor):
        return True

    if isinstance(f, (Callable, str, int)):
        return False

    return all(
        isinstance(x, Mor) or (
            isinstance(x, tuple)
            and isinstance(x[1], Mor)
        ) for x in f
    )

def _resolve_labeled(t: LabeledTransform, source: Obj):
    if isinstance(t, (Mor, Callable, str, int)):
        return resolve(t, source)

    l, t = t
    return l, resolve(t, source)