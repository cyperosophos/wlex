from typing import Callable

from .model.category import Obj, Mor, Composition
from .model import cart
from .model import lex
from .variadic.category import Transform, CartMor, LabeledMor, CartTransform, tcompose
from .variadic.cart import pairing
from .variadic.lex import lift, equalizer
from .variadic import resolve
from .equality import Eq as GeneralEq, Verifier
from .proven.cart import terminal_mor

Eq = GeneralEq[Mor]

def _check_signature(mor: Mor, source: Obj, target: Obj):
    if mor.source != source:
        raise ValueError('Wrong source')

    if mor.target != target:
        raise ValueError('Wrong target')

def _fix_eq_signature(left: Transform | Obj, right: Transform | Obj):
    if isinstance(left, Obj):
        left = Composition(left)

    if isinstance(right, Obj):
        right = Composition(right)

    if isinstance(left, (Callable, str, int)):
        if isinstance(right, (Callable, str, int)):
            raise ValueError("Sides can't be both callable.")

        left = resolve(left, right.source)
    elif isinstance(right, (Callable, str, int)):
        right = resolve(right, left.source)

    return left, right

class Context:
    __slots__ = ('refs', 'proofs', 'null_param')
    refs: dict[str, Obj | Mor]
    proofs: Verifier[object]
    null_param: cart.NullParam

    class Param(cart.Param):
        def __init__(self, x: Obj, y: Obj, label: str):
            if isinstance(x, lex.Equalizer) or isinstance(y, lex.Equalizer):
                raise ValueError("Equalizer objects are not allowed as param")

            super().__init__(x, y, label)

    def __init__(self):
        self.refs = {}
        self.proofs = Verifier(set())
        self.null_param = cart.NullParam()
        #self.null_coparam = NullCoparam() # Place this in a subclass

    def compose(self, *factors: CartTransform | Obj):
        # Straightening has to work with extensivity in the same way,
        # i.e. by composing and precomposing with inclusions as needed.
        def tm(src: Obj) -> Mor:
            return terminal_mor(cart.NullSpan(src, self.null_param))

        return tcompose(factors, self.fit_factor, tm)

    # def fix_fork(self, f: ) -> Mor:
    #     # T
    #     pass

    # def fit_for_pairing(self, mor: Mor, source: Obj, target: Obj) -> Mor:
    #     # Fit target first, since then the source may change.
    #     mor = self.fit_mor_factor(target, mor)

    #     # To get the intersection lift an identity.
    #     # Type-checking??
    #     # Do all this inside pairing??
    #     i = self.fit_mor_factor(source, identity(mor.source))
    #     j = self.fit_mor_factor(mor.source, i)
    #     return compose((mor, j))

    def fit_tuple_factor(self, target: Obj, factor: tuple[LabeledMor, ...]) -> Mor:
        if not isinstance(target, cart.Product):
            raise ValueError('Target must be product')

        return pairing(factor, target, self.fit_mor_factor, equalizer)

    def fit_mor_factor(self, target: Obj, factor: Mor) -> Mor:
        # Cases (Obj, Equalizer, Product, EP)
        # Obj -> Equalizer: restrict, lift; same superobject.
        # Equalizer -> Obj: incl; same superobject.
        # Equalizer -> Equalizer: restrict, lift, incl; same superobject.
        # Obj -> Product: isoproj; object is single component.
        # Product -> Obj: proj (explicit unless object appears only once); object is component.
        # Product -> Product: proj; shrinking components.
        # EP -> EP: same superobject, shrinking components (which first??).
        # Obj -> Terminal.

        # TODO: !!! This should be called only after not being able to match the target!
        if isinstance(target, lex.Equalizer):
            # This is needed even for fitting "obvious" isomorphic equalizers.
            # TODO: What if product conversion is needed?
            factor = lift(factor, target, self.proofs)
        elif isinstance(target, cart.Product):
            # Postcompose with a pairing.
            # TODO: Check that all of this works when one target is an
            # equalizer of a product and the other a product of equalizers.
            # It seems a product of equalizers should be converted to the equalizer
            # of a product. This is analogous to expanding using the distributive law.
            # Then the product in `factor.target` gets converted to the product in `target`.
            pass

        # In the case that there are no requirements for lifting
        # (target is not an Equalizer), we don't know that factor.target
        # is target. If `factor.target` already satisfies all requirements,
        # then `factor.target` is included in `target` (in particular superobjects
        # coincide.) If there are requirements, then when checking the
        # parallels of the fork we indirectly make sure that factor.target
        # is a subobject of target (or rather can be turned into a subobject
        # by restricting factor.source).
        # This actually a morphism with target `target`.
        # It is more simplified to only lift the inclusion as opposed
        # to the composition.
        # Notice that factor.target can only be isomorphic to target,
        # so a lift of the inclusion is always needed.
        return factor.incl(target)

    def fit_factor(self, target: Obj, factor: CartMor) -> Mor:
        if isinstance(factor, Mor):
            return self.fit_mor_factor(target, factor)

        return self.fit_tuple_factor(target, factor)

    def obj(self, name: str, cell: Obj | None = None):
        # Builtin cells (including equalities) come from the theory.
        # For cells that need a signature, the theory provides a function
        # taking the signature, since there is no point in having the signature
        # beforehand (when there are in fact no cell to define it).
        if cell is None:
            res = self.refs[name]
            if not isinstance(res, Obj):
                raise ValueError("Not an object")

            return res

        if name in self.refs:
            raise ValueError("Can't reuse name")

        cell.name = name
        self.refs[name] = cell
        return cell

    def mor(
        self, name: str,
        source: Obj | None = None, target: Obj | None = None,
        cell: Transform | None = None,
    ):
        if cell is None:
            res = self.refs[name]
            if not isinstance(res, Mor):
                raise ValueError("Not a morphism")

            return res

        if isinstance(cell, (Callable, str, int)):
            if source is None:
                raise ValueError("Source is required")

            cell = resolve(cell, source)
        elif source is None:
            source = cell.source

        if target is None:
            target = cell.target

        if name in self.refs:
            raise ValueError("Can't reuse name")

        _check_signature(cell, source, target)
        cell.name = name
        self.refs[name] = cell
        return cell

    @staticmethod
    def axiom(left: Transform | Obj, right: Transform | Obj):
        return Eq(*_fix_eq_signature(left, right))

    def eq(
        self,
        left: Transform | Obj, right: Transform | Obj,
        cell: Eq | None = None,
    ):
        left, right = _fix_eq_signature(left, right)

        # Axiomatic equalities can't be present in the proofs from the start,
        # because one does not have the cells to build their signature.
        _check_signature(right, left.source, left.target)
        proofs = self.proofs
        if cell is None:
            if Eq(left, right) in proofs:
                return

            raise ValueError("No proof")

        s = cell.s
        t = cell.t

        # Transitivity and symmetry
        if Eq(s, left) in proofs and Eq(t, right) in proofs:
            return

        if Eq(t, left) in proofs and Eq(s, right) in proofs:
            return

        # TODO: Check old context code to see how for example an equality of pairings
        # gets decomposed into multiple equalities, etc. Also check the last notes in NOTES3.

        raise ValueError("Invalid proof")

    # All functions such as compose, pairing etc. need to
    # be wrapped (functionalized) so that they can take Eq[args]
    # as argument. Can from_tuple be obtained this way?
    # Check where it is being used! Notice that a pairing
    # with an equality component makes an equality of pairings,
    # cf. Fork. `from_tuple` is the functionalization of tuple,
    # i.e. metapairing.

    # Support for __and__ in Mor and Obj? Point to context for
    # finding proofs during application of transitivity?
    # (may need to use weakref!).

    # Equal forks make equal lifts, but equality of forks is complicated
    # by the fact that parallel corresponds to a functor.
    # Indeed two parallels with the same morphims need not produce the
    # same equalizer (as e.g. the requirements have extra data corresponding
    # to their actual sources). The two equalizers are only isomorphic.
    # Cf. the labeling extra data of products.
    # The construction of the isomorphism should follow from the lift ~= fork isomorphism.

    # Go back to pullback Parallel? Parallel.__eq__ would have to be reconsidered.
    # The source of `product` is a product.
    # Product is unique *up to unique isomorphism*.
    # Pairings are equal when target products are the same.
    # Many pairings with different product targets (isomorphic) to one span.
    # How does this fit with the bijection definition of limit?
    # The answer is that this bijections occurs with respect to the specific
    # functors forming the adjunction, the right adjoint being the product.
    # So product is the functor mapping to specific objects (no anafunctors!).
    # Labeling gives isomorphic product functors, each of which has its own
    # Pairing ~= Span isomorphism (Span need not be tied to labels, but Pairing
    # does since its tied to the Product).
    # The extra data is not in the diagram functor but in the limit functor.
    # In the case of the equalizer the extra data is the sources of the requirements
    # which get intersected to form the common source of the parallel.
    # *There is the problem that this extra data appears to be useless, so we
    # should remove it with normalization.* Also, the way this extra data can be
    # tied to the limit functor is messy since it depends on the morphisms making the parallel.

    # What about the naturality of the bijection? The morphism part of the limit functor?
    # Notice that the bijection can be obtained even when fixing the diagram of the limit.

    # Allowing intensional equality of objects would require additional use of Verifier
    # in `proven`.

    # Recall that === equalities are only introduced in programs based on the theory
    # (by the use of eq ... == ...) for elements of Mor. One does not want these
    # equalities to pollute Obj, functor like types (e.g. diagrams, not to be confused
    # with functor like morphisms, e.g. limits), etc. `source @ $mor @ equalizer` is the actual equalizer.

    # *Intensional equality of equalizers?*
    # Two morphisms can only be (intensionally) equal if their source and target
    # are a priori equal. Hence equality of source and target remains extensional.

    # One can let diagrams proliferate and the bijection would still remain!
    # The bijection allows proving uniqueness up to unique isomorphism.
    # The result of equal morphism pairs in forks is a commutative triangle
    # where two sides are lifts and the third one is the unique isomorphism.

    # Notice that using "proper" diagram types (i.e. not limits, including in the case of product)
    # eliminates the finite completeness by not making the diagram explicitly constructible
    # for arbitrary components. One would possibly end up with a partial adjunction definition
    # of a partial limit. After all, the bijection applies for fixed diagrams (naturality?).

    # *Programmatic equality types?*
    # This would help avoiding equality pollution.
    # In the case of Mor, the equality types would be indexed by source and target.
    # This seems to have very limited utility.
    # An equality `eq ==` can be interpreted as a morphism
    # from the equality type of the source to the equality type of the target.
    # f == g: A= -> B=: x ~ y |-> f(x) ~ g(y) (cf. nat trans h |-> a_Y F(h))
    # f === g is shorthand for an equality type component in a certain pullback.

    # TODO: Check is_fork in `proven`!

    # x ~ y is an element of A=. For example `eq ... == ...` in the program
    # is an element of Mor=.
    # Is the following "external eq" true?
    # compose @ ((parallel_i @ $par, $mor) == (parallel_j @ $par, $mor)) @ equalizer
    # Notice that extracting this equality into a "external eq" would be nonsensical
    # as then the equality would have to be fulfilled by all fork-like products.
    # The external eq is true because the equality component of the fork guaranties
    # that we can always contruct the equality from the parallel (and therefore from
    # equality of parallels by traversing the two sides of a comsquare as in nat trans).

    # NOTICE: A program introduces elements of the three cell kinds, but more appropriately
    # one should say that even this elements are introduced by the theory
    # (perhaps the highest level, the builtin level). A program simply allows naming elements
    # (or even functions, if macros are supported).
    # To build an element of an equalizer one needs an element of the superobject
    # and an equality of elements of the target of the parallel (i.e. an element of an equality type).
    # A Fork can therefor be defined as an equalizer.