"""Cart cell classes"""
from typing import TypeGuard, override
from collections.abc import Sequence, MutableSequence
from abc import ABCMeta

from ..cells import Obj, Mor, Eq, PrimObj, PrimMor, PrimEq
from .category import CategoryObj, CategoryMor, CategoryEq, Composition

    # TODO: This goes is cart.Mor
    # def eql(self, x: cells.Mor):
    #     from ..category import Comp
    #     if super().eql(x):
    #         return True
    #     if isinstance(x, Comp):
    #         # Defer to Comp.__eq__.
    #         # This is especially useful in the case of p_eq, q_eq of pairing.
    #         return x.eql(self)
    #     return False

        # Composing pairing with projection (or with pairing of projections)
        # results in single morphism (or pairing), so this should be handled
        # by Mor.compose.
        # TODO: Because equal morphisms must have the same hash,
        # CartComp must accommodate p_eq.
        # Variadic functions with conversions, etc. of course cannot be the result of compiling
        # the ambient theory, as this would be too complicated (although accomplishable with List, etc.),
        # so they are built on simple functions which take care of type checking the arguments.
        # What about the rest of the body of such complicated functions? Just assume the return type is correct.
        # The instantiation functions (obj, mor, eq) are also not part of the theory.

class CartObj(CategoryObj, metaclass=ABCMeta):
    """Models object `cart.Obj`"""
    __slots__ = ()

    @override
    @staticmethod
    def terminal():
        return Product()

    @override
    def terminal_mor(self):
        return ProductMor(self, ())

    @override
    def product(self, y: Obj):
        x = self
        return Product(('x', x), ('y', y))

class CartPrimObj(PrimObj, CartObj):
    """Models object `cart.Obj` as primitive"""
    __slots__ = ()

class CartMor(CategoryMor, metaclass=ABCMeta):
    """Models object `cart.Mor`"""
    __slots__ = ()

    @override
    def pairing(self, q: 'Mor'):
        p = self
        return ProductMor(p.source, (('p', p), ('q', q)))

    @override
    def pairing_unique(self, p: Mor, q: Mor):
        mor = self
        return Eq(p.pairing(q), mor)

class CartPrimMor(PrimMor, CartMor):
    """Models object `cdoneart.Mor` as primitive"""
    __slots__ = ()

CartEq = CategoryEq
CartPrimEq = PrimEq

def _isinstance_sequence_object(x: object) -> TypeGuard[Sequence[object]]:
    return isinstance(x, Sequence)

def _isinstance_mutable_sequence_object(x: object) -> TypeGuard[MutableSequence[object]]:
    return isinstance(x, MutableSequence)

LabeledObj = tuple[str, Obj] | tuple[tuple[str, ...], 'Product']
ComponentName = int | str | Obj
LabeledMor = tuple[str | tuple[str, ...], Mor]

class Product(CartObj):
    """Models object corresponding to source of span `cart.product`"""
    __slots__ = 'components', 'names'
    components: dict[ComponentName, tuple[int, Obj]]
    names: list[ComponentName]

    @override
    def proj(self, name: object):
        if name in self.components:
            assert isinstance(name, ComponentName)
            return Proj(name, self)

        if isinstance(name, int):
            if name >= len(self.components):
                raise ValueError("`name` of type `int` is out of range.")
            return Proj(self.pos_to_name(name), self)

        raise ValueError("`name` does not correspond to any component.")

    def __new__(cls, *params: LabeledObj):
        if not params:
            if not hasattr(cls, '_terminal'):
                cls._terminal = super().__new__(cls)

            return cls._terminal

        return super().__new__(cls)

    def name_to_obj(self, name: ComponentName):
        """Get the object associated to `name` in components

        `name` of type `int` only works if there is no name of other type for
        the corresponding component. This will raise `KeyError` if `name` does
        not correspond to any component.
        """
        return self.components[name][1]

    def _add_name(self, name: ComponentName, obj: Obj):
        if isinstance(name, str):
            if name in self.components:
                _, t = self.components[name]

                if not t.identical(obj):
                    raise ValueError(
                        "Repeated name requires repeated associated object.",
                    )

                return
        elif isinstance(name, Obj):
            assert name is obj

            if name in self.components:
                name = len(self.components)
        else:
            name = len(self.components)

        self.components[name] = (len(self.components), obj)

    def pos_to_obj(self, pos: int):
        """Get the object occupying position `pos` in components

        This will raise an `IndexError` if `pos` is outside range.
        """
        return self.components[self.names[pos]][1]

    def pos_to_name(self, pos: int):
        """Get the name occupying position `pos` in components

        This will raise an `IndexError` if `pos` is outside range.
        """
        return self.names[pos]

    def pos_to_name_and_obj(self, pos: int):
        """Get the name and object occupying position `pos` in components

        This will raise an `IndexError` if `pos` is outside range.
        """
        name = self.names[pos]
        return name, self.components[name][1]

    def _add_names(self, names: tuple[str, ...], obj: 'Product'):
        if len(names) != len(obj.components):
            raise ValueError("Tuple of names must have same length as product.")

        for i, subname in enumerate(names):
            # Repeated subnames are allowed, they get handled by `_addname`.
            if subname:
                self._add_name(subname, obj.pos_to_obj(i))
            else:
                # An empty subname will keep the original subname. This means
                # that, in the case of a named product subparam, no further
                # unpacking will occur, it will remain as a product param.
                self._add_name(*obj.pos_to_name_and_obj(i))

    def __init__(self, *params: LabeledObj):
        # Repeated component names are allowed. This is based on the fact that
        # AxBxC is the pullback of the projections AxB->B and BxC->B.
        if (
            not params and self is self._terminal
            and hasattr(self, 'components')
        ):
            return

        # Component value includes position.
        self.components = {}

        if len(params) == 1:
            name, obj = params[0]
            if isinstance(obj, Product):
                # This needed to be able to treat `(x,)` and `x` as the same.
                raise ValueError(
                    "Can't have instance of `Product` as single component",
                )
            if not name:
                raise ValueError("Can't have nameless single component")

        for arg in params:
            name, obj = arg
            if isinstance(name, tuple):
                if not isinstance(obj, Product):
                    raise TypeError(
                        "An object associated to a tuple of names must be an "
                        "instance of `Product`.",
                    )
                # Names of product components get overridden here.
                self._add_names(name, obj)
            elif name:
                self._add_name(name, obj)
            elif isinstance(obj, Product):
                for subname, (_, t) in obj.components.items():
                    self._add_name(subname, t)
            else:
                # The obj is the name.
                self._add_name(obj, obj)
        self.names = list(self.components.keys())

    def identical(self, x: Obj):
        return super().identical(x) or (
            isinstance(x, Product)
            and all(
                n == m and s.identical(t)
                for (n, (_, s)), (m, (_, t))
                in zip(self.components.items(), x.components.items())
            )
        )

    def hint(self):
        return ((n, s) for n, (_, s) in self.components.items())

    def get_from_sequence(self, x: Sequence[object], name: ComponentName):
        """Get component corresponding to name from `x`

        `name` of type `int` only works if there is no name of other type for
        the corresponding component. This will raise `KeyError` if `name` does
        not correspond to any component, and `IndexError` if `x` does not have
        enough items.
        """
        # No need to check here whether `x` is accepted by `self`.
        return x[self.components[name][0]]

    def accepts(self, x: object):
        if _isinstance_sequence_object(x):
            if len(x) != len(self.components):
                return False

            return all(
                obj.accepts(self.get_from_sequence(x, name))
                for name, (_, obj) in self.components.items()
            )

        if 1 != len(self.components):
            return False

        return self.pos_to_obj(0).accepts(x)

    def same(self, x: object, y: object):
        _x, _y = (
            v if _isinstance_sequence_object(v) else (v,)
            for v in (x, y)
        )
        _gfs = self.get_from_sequence
        return all(
            typ.same(_gfs(_x, name), _gfs(_y, name))
            for name, (_, typ) in self.components.items()
        )

    def __str__(self):
        name = super().__str__()
        if name is NotImplemented:
            components = (
                f'{n}: {typ}' if isinstance(n, str) else f'{typ}'
                for n, (_, typ) in self.components.items()
            )
            return f'({', '.join(components)})'
        return name

    def __repr__(self):
        return f'`product {self!s}`'

class Proj(CartMor):
    "Models morphism corresponding to projection"
    __slots__ = ('component_name',)

    def __init__(self, name: ComponentName, source: Product):
        # Instantiation occurs by calling `source.proj`, which takes care of
        # checking `name`.
        self.component_name = name
        target = source.name_to_obj(name)
        super().__init__(source, target)

    def ev(self, x: object):
        # `x` is accepted by source (as can be checked in `self.public_ev`) is
        # proof enough that the result of `self.ev` is accepted by `target`. The
        # point of defensive evaluation is to check that the target accepts the
        # result when this is not guaranteed by having the source accept the
        # argument.
        source = self.source
        assert isinstance(source, Product)
        if _isinstance_sequence_object(x):
            return source.get_from_sequence(x, self.component_name)
        # Required for single component product.
        return x

    def same(self, x: Mor):
        if super().same(x):
            return True
        return (
            isinstance(x, Proj)
            and self.name == x.name
            and self.source.identical(x.source)
        )

    def hint(self):
        return self.name, self.source

    def __str__(self):
        name = super().__str__()
        if name is NotImplemented:
            cname = self.component_name
            if isinstance(cname, (int, str)):
                return f'{cname}$'
            return str(cname)
        return name

    def __repr__(self):
        return f'`proj {self!s}[{self.source}]`'

class ProductMor(CartMor):
    """Models object corresponding to source of span `cart.product`"""
    __slots__ = ('components',)

    # The names are in the target. The bool is the unpack flag.
    components: list[tuple[bool, Mor]]

    @staticmethod
    def _load_consistency(mor_to_eq: dict[Mor, Eq], consistency: Sequence[Eq]):
        # No renaming here, only composition with projections. The equality in
        # consistency may relate overlapping morphisms (with product targets).
        # In this case the setoid source and targets may be the morphisms
        # composed with projections. Consistency equality must have first
        # occurrence of repeated morphism as setoid source.
        for e in consistency:
            et = e.starget

            if et in mor_to_eq:
                raise ValueError(
                    "Can't have two consistency equalities with the same "
                    "setoid target",
                )

            mor_to_eq[et] = e

    @staticmethod
    def _add_name(
        name_to_mor: dict[ComponentName, Mor], mor_to_eq: dict[Mor, Eq],
        name: ComponentName, mor: Mor,
    ):
        # Returns True when `mor` gets added
        if isinstance(name, str):
            if name in name_to_mor:
                m = name_to_mor[name]

                if mor in mor_to_eq:
                    e = mor_to_eq[mor]
                else:
                    raise ValueError(
                        "Needs equality of morphisms with the same name"
                    )

                if not e.ssource.same(m):
                    raise ValueError(
                        "Found equality but without required signature"
                    )
                return False
        elif isinstance(name, Obj):
            assert name is mor.target

            if name in name_to_mor:
                name = len(name_to_mor)
        else:
            name = len(name_to_mor)

        name_to_mor[name] = mor
        return True

    def _add_names(
        self, name_to_mor: dict[ComponentName, Mor], mor_to_eq: dict[Mor, Eq],
        names: tuple[str, ...], mor: Mor,
    ):
        obj = mor.target
        if not isinstance(obj, Product):
            raise TypeError(
                "A morphism associated to a tuple of names must have "
                "an instance of `Product` as target."
            )

        if len(names) != len(obj.components):
            raise ValueError(
                "Tuple of names must have same length as product (target of "
                "morphism).",
            )
        # Make a renaming pairing to compose with morphism. The pairing
        # may end up not including all components of the target of
        # morphism. Consistency equality applies to the morphism
        # composed with the projection corresponding to the name of
        # component in the target of the morphism.

        # The component morphisms are registered (after possibly
        # composing with renaming) in the same order they are executed.
        # Their output is concatenated and exactly corresponds to the
        # target product.
        renaming: list[tuple[str, ComponentName]] = []
        for i, subname in enumerate(names):
            origname = obj.pos_to_name(i)

            # Public type checking guarantees that this passes
            # (dependent) type checking.
            pmor = obj.proj(origname).compose(mor)

            n = subname or origname
            if self._add_name(name_to_mor, mor_to_eq, n, pmor):
                renaming.append(
                    (n if isinstance(n, str) else '', origname),
                )

        # ProductMor instance here may actually end up being just a terminal
        # morphism, which means that all components of the result of morphism
        # get deleted.
        return (names, obj), (True, ProductMor(obj, [
            (new, obj.proj(old)) for new, old in renaming
        ]).compose(mor))

    def _add_str_name(
        self, name_to_mor: dict[ComponentName, Mor], mor_to_eq: dict[Mor, Eq],
        name: str, mor: Mor,
    ):
        obj = mor.target
        # No renaming here, only deletions of repeated morphisms.
        if name:
            if self._add_name(name_to_mor, mor_to_eq, name, mor):
                component = False, mor
            else:
                component = True, ProductMor(mor.source, ())
        elif isinstance(obj, Product):
            segment: list[str] = []
            for subname in obj.names:
                pmor = obj.proj(subname).compose(mor)
                if self._add_name(
                    name_to_mor, mor_to_eq, subname, pmor,
                ):
                    segment.append(
                        subname if isinstance(subname, str) else '',
                    )

            if len(segment) == len(obj.components):
                # Register the whole morphism, no need for deletions
                component = True, mor
            else:
                # ProductMor instance here may be terminal morphism.
                component = True, ProductMor(obj, [
                    (m, obj.proj(m)) for m in segment
                ]).compose(mor)
        else:
            if self._add_name(name_to_mor, mor_to_eq, obj, mor):
                component = False, mor
            else:
                component = True, ProductMor(mor.source, ())

        return (name, obj), component

    def _update_components(
        self, target_params: list[LabeledObj], param: LabeledObj,
        component: tuple[bool, Mor], _terminal: Obj = Product(),
    ):
        # Based on having no assumptions about implementation and functions
        # being pure it makes sense to discard functions whose return values
        # would be discarded. The repeated functions are not fallbacks.
        target_params.append(param)
        # Terminal morphisms get exluded in order to facilitate comparison
        # through `same`.
        if not component[1].target.identical(_terminal):
            self.components.append(component)

    def __init__(
        self, source: Obj, params: Sequence[LabeledMor],
        consistency: Sequence[Eq] = (),
    ):
        # A pairing of all the projection of a product is the identity of the
        # product. We let this equality be handled intensionally, especifically
        # through `pairing_unique`. Handling it extensionally seems of limited
        # usefulness. However, composing with a pairing of projections is
        # handled extensionally, in this context the pairing of all projects
        # acts as the identity.

        # Consistency equalities are provided as arguments along with morphisms
        # even in the high-level interface. One identifies equalities based on
        # their setoid source and target. This is possible even in the case
        # where there is overlap of product targets. In this case the morphisms
        # related by the equality are composed with projections (or only the
        # morphism with product target).

        # In the case of pairing for assigment, the pairing always includes the
        # identity as its first component. Reassigning would thus require a
        # consistency equality to prove that the value is not being changed
        # (no clear use case for this). Actually changing the value would
        # therefore require removing the old value (through a pairing of
        # projections).

        # `source` must be the source of morphisms in param. This is checked in
        # the public interface (just like matching source and target is checked
        # in the case of composition, for example).
        if len(params) == 1:
            name, mor = params[0]
            if isinstance(mor.target, Product):
                raise ValueError(
                    "Can't have morphism with target `Product` as single "
                    "component",
                )
            if not name:
                raise ValueError(
                    "Can't have nameless single component morphism",
                )

        self.components = []
        target_params: list[LabeledObj] = []
        name_to_mor: dict[ComponentName, Mor] = {}
        mor_to_eq: dict[Mor, Eq] = {}

        self._load_consistency(mor_to_eq, consistency)

        for arg in params:
            name, mor = arg

            if isinstance(name, tuple):
                self._update_components(target_params, *self._add_names(
                    name_to_mor, mor_to_eq, name, mor,
                ))
            else:
                self._update_components(target_params, *self._add_str_name(
                    name_to_mor, mor_to_eq, name, mor,
                ))

        target = Product(*target_params)
        assert len(name_to_mor) == len(target.components)
        assert all(j == k for j, k in zip(name_to_mor, target.components))
        super().__init__(source, target)

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, ProductMor)
            and self.target.identical(x.target)
            and all(
                u == v and s.same(t)
                for (u, s), (v, t)
                in zip(self.components, x.components)
            )
        )

    def hint(self):
        return self.source, self.target, self.components

    def ev(self, x: object):
        # In the case of the local namespace (regarded as Product instance)
        # there is a special composition that makes sure that linearity is
        # respected. Right before the return, the local namespace is made
        # inmutable, so that it can for example be safely returned, duplicated,
        # etc.
        def _extend(res: MutableSequence[object], unpack: bool, mor: Mor):
            r = mor.ev(x)
            if unpack:
                assert _isinstance_sequence_object(r)
                res.extend(r)
            else:
                res.append(r)

        components = self.components
        if len(components) >= 1:
            first = components[0][1]
            if _is_identity(first) and _isinstance_mutable_sequence_object(x):
                # `first` is the local namespace and the remaining components
                # are the assignments.
                for i in range(1, len(components)):
                    _extend(x, *components[i])

                return x

        _res: list[object] = []
        for c in components:
            _extend(_res, *c)

        return tuple(_res)

def _is_identity(mor: Mor):
    # Identity in an extensional sense
    return isinstance(mor, Composition) and mor.factors == ()

class CartComposition(Composition, CartMor):
    """Handles extra conditions that make two morphisms the same

    The extra condition is the one coming from composition of pairing and
    projection.
    """
    # TODO: override CartMor.same to handle terminal morphisms.

    @staticmethod
    def _

    def __init__(self, target: Obj | Mor, *factors: Mor):
        super().__init__(target, *factors)

        _factors: list[Mor] = []
        factor_it = iter(self.factors)
        for _ in factor_it:
            break

        # This is wrong in the sense that factor2 may be changed the previous iteration!
        for factor1, factor2 in zip(self.factors, factor_it):
            # (f @ a$, g @ b$) @ (a=m, b=n)
            # becomes (f @ m, g @ n)
            # (f @ a$, g @ b$) @ p
            # can't become (f @ a$p, g @ b$p)
            # The idea is then that if a morphism gets repeated during simplification
            # then simplification doesn't go through.
            _is_projs(factor1)

        if len(_factors) == 1:
            # Before instantiating one must make sure that composing pairings
            # and projections does not result in single factor.
            raise ValueError(
                "Composing projections with pairings gives single factor.",
            )
