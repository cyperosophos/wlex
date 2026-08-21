from typing import Callable

from .model.category import Obj, Mor
from .equality import Eq as GeneralEq, Verifier

Eq = GeneralEq[Mor]

class PlaceholderObj(Obj):
    __slots__ = ('_accepts',)
    _accepts: Callable[[object], bool]

    def accepts(self, x: object) -> bool:
        return self._accepts(x)

    def set_accepts(self, fn: Callable[[object], bool]):
        self._accepts = fn

class PlaceholderMor(Mor):
    __slots__ = ('_ev',)
    _ev: Callable[[object], object]

    def ev(self, x: object) -> object:
        return self._ev(x)

    def set_ev(self, fn: Callable[[object], object]):
        self._ev = fn

def _check_signature(mor: Mor, source: Obj, target: Obj):
    if mor.source != source:
        raise ValueError('Wrong source')

    if mor.target != target:
        raise ValueError('Wrong target')

def _check_eq(eq: Eq, left: Mor, right: Mor, proofs: Verifier[object]):
    if (eq, Eq(left, right)) not in proofs:
        raise ValueError('Invalid proof')

class Context:
    __slots__ = (
        'refs',
        'eqs', 'unproven_eqs',
        'ph_names',
        'proofs',
    )
    refs: dict[str, Obj | Mor]
    # TODO: Do these equalities ever get used by the Verifier??
    # It appears Verifier would handle equalities from the theory not from the program.
    # However, extensional equalities are already __eq__ based. So what's the point of Verifier??
    eqs: set[Eq]
    unproven_eqs: set[Eq]
    ph_names: set[str]
    proofs: Verifier[object]

    def obj(self, name: str, cell: Obj | None = None):
        # Builtin names come from the theory.

        if name in self.refs:
            raise ValueError("Can't reuse name")

        if cell is None:
            cell = PlaceholderObj()
            self.ph_names.add(name)

        cell.name = name
        self.refs[name] = cell
        return cell

    def mor(
        self, name: str,
        source: Obj, target: Obj,
        cell: Mor | None = None,
    ):
        if name in self.refs:
            raise ValueError("Can't reuse name")

        if cell is None:
            cell = PlaceholderMor(source, target)
            self.ph_names.add(name)
        else:
            _check_signature(cell, source, target)

        cell.name = name
        self.refs[name] = cell
        return cell

    def eq(
        self,
        left: Mor, right: Mor,
        cell
    ):
        # `eq f == g;` can also be interpreted as proof? No! It is a signature!
        # Proofs (like definitions) occur before their use. This avoids circular refs!
        _check_signature(right, left.source, left.target)
        cell = Eq(left, right)
        if cell not in self.eqs:
            self.unproven_eqs.add(Eq(left, right))
        #else:
        #    _check_eq(cell, left, right, self.proofs)
        #    self.proven_eqs.add(cell)

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