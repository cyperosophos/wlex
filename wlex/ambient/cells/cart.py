"""Cart cell classes"""
from typing import Self, TypeGuard, override
from collections.abc import Sequence, Mapping, Iterable
from abc import ABCMeta

from ..cells import Obj, Mor, PrimMor, TypeObj, PrimEv
from .category import (
    CategoryObj, CategoryMor, CategoryEq, CategoryPrimEq, Composition,
    CategoryAxiom,
)

class CartObj(CategoryObj, metaclass=ABCMeta):
    """Models object `cart.Obj`"""
    __slots__ = ()

    _product_cls: type['Product']
    _product_mor_cls: type['ProductMor']

    @classmethod
    def init_cls(cls):
        cls._eq_cls = CartEq
        cls._composition_cls = CartComposition
        cls._product_cls = Product
        cls._product_mor_cls = ProductMor

    @override
    @classmethod
    def terminal(cls):
        return cls.vproduct(())

    @override
    def terminal_mor(self):
        return self.vproduct_mor(())

    @override
    def product(self, y: Obj):
        x = self
        return self.vproduct((('x', x), ('y', y)))

    @override
    @classmethod
    def vproduct(
        cls,
        params: Sequence[tuple[str | int, Obj]],
        no_repeat: bool = False,
    ):
        return cls._product_cls(params, no_repeat=no_repeat)

    @override
    def vproduct_mor(
        self,
        params: Sequence[tuple[str | int, Mor]],
    ):
        # Handle case of unlabeled morphism with product target
        if len(params) == 1:
            l, c = params[0]
            if l == '' and isinstance(c.target, Product):
                return c

        res = self._product_mor_cls(self, params)
        if res.is_proj() and self.identical(res.target):
            return self.identity()

        return res

    # @override
    # def join(self, obj: Obj):
    #     # In the case of product this is the largest product that appears as the
    #     # target of (pairing of) projections with the same labels from both
    #     # objects. Notice that objects, treated as unlabeled single component
    #     # products, are considered to coincide with the corresponding component
    #     # in a product, even when this component is necessarily labeled, so that
    #     # one morphism is the identity while the other is a projection with a
    #     # label. This is a slight inconsistency. Also, if the object is a
    #     # product it may also appear as several components. We try first finding
    #     # it as a single component. `join` is commutative.
    #     # Alternatively: avoid the inconsistency alltogether. Consider only
    #     # (pairings of) projections and terminal morphisms. This makes more sense
    #     # considering that an object can appear more than once as a component but
    #     # with different labels.
    #     if self.identical(obj):
    #         return (self.identity(), obj.identity())

    #     return (self.terminal_mor(), obj.terminal_mor())

    @override
    def trim_join(self, obj: Obj) -> Obj:
        if self.sup.identical(obj.sup):
            return self.sup

        return self.terminal()

class CartTypeObj(TypeObj, CartObj):
    __slots__ = ()

class CartMor(CategoryMor, metaclass=ABCMeta):
    """Models object `cart.Mor`"""
    __slots__ = ()

    @override
    def same(self, x: Mor):
        # We handle sameness of terminal morphisms here.
        terminal = self.source.terminal()
        return super().same(x) or (
            self.target.identical(terminal)
            and x.target.identical(terminal)
            and self.source.identical(x.source)
        )

    @override
    def pairing(self, q: Mor):
        p = self
        return p.source.vproduct_mor((('p', p), ('q', q)))

    @override
    def pairing_unique(self, p: Mor, q: Mor):
        mor = self
        eq = self.source.postulate(p.pairing(q), mor)
        eq.proven = True
        return eq

class CartPrimMor(PrimMor, CartMor):
    """Models object `cart.Mor` as primitive"""
    __slots__ = ()

class CartPrimEv(PrimEv):
    __slots__ = ()

    def to_mor(self, source: Obj, target: Obj):
        return CartPrimMor(source, target, self.func)

CartEq = CategoryEq
CartPrimEq = CategoryPrimEq
CartAxiom = CategoryAxiom

class ComponentMap[T](Mapping[str | int, T]):
    __slots__ = '_map', '_data', 'tup'

    _map: dict[str | int, T] | None # Contains only values with non-empty labels
    _data: frozenset[tuple[str | int, T]] | None
    tup: tuple[T, ...]

    @property
    def data(self) -> frozenset[tuple[str | int, T]]:
        if self._data is None:
            return frozenset(enumerate(self.tup))

        return self._data

    def __init__(self, data: Sequence[tuple[str | int, T]]):
        if set(range(len(data))) == set(k for k, _ in data):
            self._map = None
            self._data = None
            self.tup = tuple(c for (_, c) in sorted(data))
        else:
            self._map = dict((k, v) for k, v in data if k != '')
            self._data = frozenset(data)
            self.tup = ()

    def __getitem__(self, key: str | int):
        if self._map is None:
            if isinstance(key, int):
                return self.tup[key]

            raise KeyError

        return self._map[key]

    def __iter__(self):
        if self._map is None:
            return iter(range(len(self.tup)))

        return iter(self._map)

    def __len__(self):
        if self._map is None:
            return len(self.tup)

        return len(self._map)

    def __hash__(self):
        return hash(self._data or self.tup)

    def full_eq(self, x: Self):
        if self._map is None:
            return self.tup == x.tup

        return self._data == x._data

    def full_items(self):
        if self._data is None:
            return enumerate(self.tup)

        return iter(self._data)

    def full_len(self):
        if self._data is None:
            return len(self.tup)

        return len(self._data)

    def __repr__(self):
        if self._data is None:
            return ', '.join(repr(c) for c in self.tup)

        return ', '.join(f'{l} = {c}' for l, c in self.full_items())

class Product(CartObj):
    """Models object corresponding to source of span `cart.product`"""
    __slots__ = ('components',)

    components: ComponentMap[Obj]

    # @override
    # def extend(self, mor: Mor):
    #     if self.identical(mor.target):
    #         return mor

    #     # Notice that in `req` one gets rid of tautologies arrising from
    #     # terminal morphisms because of these being extensionally equal
    #     # (so they get caught by the `ref` check in `prove`).

    #     # TODO: lift gets type-checked with `equalizer_pairing`.
    #     # How does this get type-checked if at all??
    #     # The idea is that one simplifies a certain composition
    #     # starting (from source) with a projection by extending
    #     # along a projection (instead of lifting along an inclusion).
    #     return self._equalizer_mor_cls(mor, self)

    # @override
    # def join(self, obj: Obj):
    #     if self.identical(obj):
    #         return (self.identity(), obj.identity())

    #     if not isinstance(obj, Product):
    #         return (self.terminal_mor(), obj.terminal_mor())

    #     data = self.components.data & obj.components.data
    #     res = tuple(ProductMor(o, [
    #         (l, o.proj(l))
    #         for l, _ in data
    #     ]) for o in (self, obj))
    #     assert len(res) == 2
    #     return res

    @override
    def trim_join(self, obj: Obj) -> Obj:
        if self.identical(obj.sup):
            return self

        if not isinstance(obj.sup, Product):
            return self.terminal()

        data = self.components.data & obj.sup.components.data
        return self.vproduct(list(data))

    def trim(self, obj: Obj):
        # Includes weakening, but not weakening unlabeled X from labeleded X x Y,
        # as this would require an inconsistent treatment of the case Y := X.
        # The ambiguity arises as well when trimming XxYx(XxY) to XxY. Hence,
        # for simplicity, trims must preserve labels. Also, the legs of a
        # trim_join must be trims.
        # TODO: At the context level, support converting through single label relabeling, i.e. projection and single component pairing.
        # Fail when there would be an ambiguity, including the ambiguity of trimming vs
        # projecting in the case of product components which also appear as multiple components
        # (flattened).
        if self.identical(obj):
            return self.identity()

        if not isinstance(obj, Product):
            raise ValueError("Can't trim to non product")

        components = self.components
        conversions: list[tuple[str | int, Mor]] = []
        for label, c in obj.components.items():
            if label not in components:
                raise ValueError("Can't trim to product with extra labels")

            conv = c.trim(components[label])
            conversions.append((label, conv))

        return self.vproduct_mor([
            (label, c.compose(obj.proj(label)))
            for label, c in conversions
        ])

    @override
    def proj(self, label: str | int):
        return Projection.from_path(self, (label,))

    def __new__(cls, components: Sequence[tuple[str | int, Obj]], no_repeat: bool = False):
        if not components:
            terminal = getattr(cls, '_terminal', None)
            if isinstance(terminal, cls):
                return terminal

            cls._terminal = super().__new__(cls)

        if len(components) == 1:
            l, c = components[0]
            if l == '' and isinstance(c, Product):
                return c

        return super().__new__(cls)

    @staticmethod
    def _add_component(
        agg: dict[str | int, Obj],
        label: str | int,
        component: Obj,
        no_repeat: bool
    ):
        if label in agg:
            if no_repeat:
                raise ValueError("No repeats allowed")

            if not component.identical(agg[label]):
                raise ValueError("Types with same label must be identical.")
        else:
            agg[label] = component

    def iso_relabeling(self, relabeling: Iterable[tuple[str | int, str | int]]):
        used: set[str | int] = set()
        for k, v in relabeling:
            yield k, v
            used.add(k)

        for key in self.components:
            if key not in used:
                yield key, key

    def sequence_relabeling(self, relabeling: Sequence[str | int]):
        # This works because if the labels are a range of numbers (from 0), then
        # they will be ordered when initializing components, so that labeling
        # based on the order of labels is the same as labeling based on their
        # values.

        # We don't check the length of `relabeling`.
        for i, label in enumerate(self.components):
            if label != '':
                yield label, relabeling[i]

    def with_labels(
        self, relabeling: Iterable[tuple[str | int, str | int]],
    ):
        # This doesn't check that there are no empty or repeated labels.

        # `with_labels` is the method to access specific components. We allow
        # accessing several components at once because this is required for
        # preserving requirements when the product is a superobject within a
        # subobject. For simplicity we avoid (de)flattening (e.g. by the use
        # repeated or empty labels), because (de)flattening would for example
        # make it difficult to preserve order, predict size, avoid overlapps,
        # etc. This means that deep relabeling is not supported by `with_labels`
        # and would have to be done through manual restating of some
        # requirements.

        terminal = self.terminal()
        # To be consistent with the way we handle projections, checking that
        # all keys correspond to components is handled at a higher level.
        return self.vproduct([
            (new, self.components.get(old, terminal))
            for old, new in relabeling
        ], no_repeat=True)

    def relabel(
        self, relabeling: Iterable[tuple[str | int, str | int]],
    ):
        return self.vproduct_mor([
            (new, self.proj(old))
            for old, new in relabeling
        ])

    def __init__(self, components: Sequence[tuple[str | int, Obj]], no_repeat: bool = False):
        super().__init__()
        # Repeated component labels are allowed. This is based on the fact that
        # AxBxC is the pullback of the projections AxB->B and BxC->B.

        # Avoid reinitializing terminal object
        if (
            not components and self is self._terminal
            and hasattr(self, 'components')
        ):
            return

        if len(components) == 1:
            l, c = components[0]
            if l == '' and isinstance(c, Product):
                return

        agg: dict[str | int, Obj] = {}
        terminal = self.terminal()
        for label, component in components:
            if label != '':
                if component is not terminal:
                    self._add_component(agg, label, component, no_repeat)
            else:
                if not isinstance(component, Product):
                    raise ValueError("Unlabeled component must be product.")

                for l, c in component.components.items():
                    assert l != ''
                    self._add_component(agg, l, c, no_repeat)

        self.components = ComponentMap(list(agg.items()))
        assert len(self.components) == self.components.full_len()

    def identical(self, x: Obj):
        return super().identical(x) or (
            isinstance(x, Product)
            and len(self.components) == len(x.components)
            and all(
                l in x.components and c.identical(x.components[l])
                for l, c in self.components.items()
            )
        )

    def hint(self):
        return self.components

    def accepts(self, x: object):
        # No type accepts None!
        return (
            _is_product_acceptable(x)
            and len(self.components) == len(x)
            and all(
                l in x and c.accepts(_gi(x, l))
                for l, c in self.components.items()
            )
        )

    def same(self, x: object, y: object):
        return (
            _is_product_acceptable(x)
            and _is_product_acceptable(y)
            and len(x) == len(y)
            and all(
                l in x and l in y and c.same(_gi(x, l), _gi(y, l))
                for l, c in self.components.items()
            )
        )

    def __repr__(self):
        return f'{type(self).__name__}({self.components})'

def _insert_or_pad(dest: list[object], idx: int, v: object):
    while idx >= len(dest):
        dest.append(None)

    assert dest[idx] is None
    dest[idx] = v

def _isinstance_tuple_object(x: object) -> TypeGuard[tuple[object]]:
    return isinstance(x, tuple)

def _isinstance_dict_str_object(x: object) -> TypeGuard[dict[str | int, object]]:
    return (
        isinstance(x, dict)
        and all(isinstance(k, (str, int)) for k in x) # pyright: ignore[reportUnknownVariableType]
    )

def _is_product_acceptable(x: object) -> TypeGuard[tuple[object] | dict[object, object]]:
    return isinstance(x, (tuple, dict))

def _is_identity(mor: Mor):
    # Identity in an extensional sense
    return isinstance(mor, Composition) and mor.factors == ()

def _is_terminal_morphism(mor: Mor):
    return mor.same(mor.source.terminal_mor())

def _gi(x: tuple[object] | dict[object, object], key: str | int):
    if isinstance(x, tuple):
        if isinstance(key, str):
            return None

        if key >= len(x):
            return None

        return x[key]

    return x.get(key)

ProjPath = tuple[str | int, ...]

class Projection(CartMor):
    "Models morphism corresponding to projection"
    __slots__ = ('path',)
    path: ProjPath

    def __init__(
        self, source: Product, target: Obj,
        path: ProjPath,
    ):
        self.path = path # polish order
        super().__init__(source, target)

    def exfit(self, source: Obj):
        # `exfit` is to `proj` (and `trim`) what `fit` is to `incl`.

        # TODO: What about equalities (cf. LexContext._straighten_eqs)
        # No extend method needed.
        # This need not preserve target. It can "overextend", which results in
        # a terminal target.

        # In the case of a pairing of projections, one extends each component,
        # so that only some of them may up needing to be composed with a
        # terminal morphism.
        # TODO: Make sure that in ProductMor, one gets rid of terminal morphism
        # components.
        # Notice that since target isn't preserved this can't be handled as simplification.
        # We actually not just extending, but also composing with a projection as needed
        # (e.g. with a terminal morphism). We can also precompose with a projection,
        # so that we handle e.g. the case where source is not a product, or there is no
        # projection (identity) from the old source to the new source. All of this makes
        # this method much closer to `fit`. However, we keep it in the cell layer since there
        # no equalities to prove. This makes type-checking unnecessary.
        # TODO: Make sure labels are being taken into account.
        if source.identical(self.target):
            # This seems somewhat inconsistent with the way `trim` works,
            # because the morphism produced by `trim` always preserves labels.
            # The result of `trim` is never a projection (but rather a pairing
            # of projections), which would be the morphism along which the
            # extension occurs here. The apparent inconsistency is justified by
            # the fact that the extending morphism can only be `self` in this
            # case, so there is no ambiguity the way there is when weakening
            # X x X to one of its components.
            return source.identity()

        if not isinstance(source, Product):
            # Precomposed extension.The extension is the identity of the
            # terminal object, and the extended morphism got composed with a
            # terminal morphism.
            return source.terminal_mor()

        # If `source` and `self.source` are identical then this will be the same
        # as `self`.
        # TODO: Context level (ex)fit must preserve name!
        return self.from_path(source, self.path)

    @classmethod
    def from_path(cls, source: Product, path: Sequence[str | int]):
        """Create projection from path"""
        target = source

        if len(path) < 1:
            raise ValueError("`path` can't be empty.")

        for label in path:
            if isinstance(target, Product):
                target = target.components.get(label)
            else:
                target = None

            if target is None:
                return source.terminal_mor()

        return cls(source, target, tuple(path))

    def proj_compose(self, mor: Self):
        """Compose with projections into a single projection"""
        source = mor.source
        target = self.target
        assert isinstance(source, Product)

        return Projection(source, target, (*mor.path, *self.path))

    def ev(self, x: object):
        for label in self.path:
            x = _gi(x, label) # pyright: ignore[reportArgumentType]

        assert isinstance(x, object)
        return x

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, Projection)
            and self.path == x.path
            and self.source.identical(x.source)
        )

    def hint(self):
        return self.path, self.source

    def __repr__(self):
        name = self.name or f"{''.join(f'{n}$' for n in self.path)}: {self.target}"
        return f'{type(self).__name__}({name})'

# TODO: Does this work well with terminal morphisms?
class ProductMor(CartMor):
    """Models object corresponding to `cart.ProductMor`"""
    __slots__ = 'components', 'inplace'

    components: ComponentMap[Mor]
    inplace: bool

    def is_proj(self, _prefix: list[str | int] | None = None) -> bool:
        if _prefix is None:
            _prefix = []

        for label, component in self.components.full_items():
            if label == '':
                return False

            if isinstance(component, ProductMor):
                _prefix.append(label)
                ip = component.is_proj(_prefix=_prefix)
                _prefix.pop()

                if not ip:
                    return False
            elif isinstance(component, Projection):
                if component.path != (*_prefix, label):
                    return False
            else:
                return False

        return True

    def exfit(self, source: Obj):
        # Call `exfit` on each component. Cf. `component_compose`.
        # TODO: Cf. trim
        return self.source.vproduct_mor([
            (label, component.exfit(source))
            for label, component in self.components.full_items()
        ])

    def after_proj(self, mor: Projection) -> Mor | tuple[Mor, Mor]:
        """Get the morphism associated to projection in the pairing

        The composition of `self` and `mor` may sometimes not reduce to a single
        morphism. This is the case when the target of the resulting morphism
        does not coincide with the target of the projection. When this occurs, a
        tuple of two morphisms is returned, the first one being the adapted
        projection and the second one being the resulting morphism.
        """
        res = self

        # Empty `path` is not allowed, since it would make Projection an
        # identity.
        for i, label in enumerate(mor.path):
            if isinstance(res, ProductMor):
                component = res.components.get(label)
                if component is not None:
                    res = component
                    continue

            # The returned projection is truncated to include all remaining
            # indices with the target of `res` as its source.
            t = res.target
            assert isinstance(t, Product)
            return Projection.from_path(t, mor.path[i:]), res

        return res

    def component_compose(self, mor: Mor):
        """Compose each component with `mor`"""
        for label, component in self.components.full_items():
            yield label, component.compose(mor)

    def idx_to_labels(self, relabeling: Sequence[str | int]):
        if len(relabeling) != len(self.components):
            raise ValueError("Wrong relabeling list length")

        return self.source.vproduct_mor([
            (relabeling[i], component)
            for i, component in enumerate(self.components.values())
        ])

    def __new__(
        cls, source: Obj,
        components: Sequence[tuple[str | int, Mor]],
    ):
        if len(components) == 1:
            l, c = components[0]
            if l == '':
                if isinstance(c, ProductMor):
                    return c

        return super().__new__(cls)

    def __init__(
        self, source: Obj,
        components: Sequence[tuple[str | int, Mor]],
    ):
        # Since this creates the target as a product this cannot be used
        # directly with morphisms with Subobject targets (e.g. EqualizerMor).
        if len(components) == 1:
            l, c = components[0]
            if l == '':
                if isinstance(c, ProductMor):
                    return

                assert not isinstance(c.target, Product)

        target = source.vproduct([(l, c.target) for l, c in components], no_repeat=True)
        mors: list[tuple[str | int, Mor]] = []
        self.inplace = False
        for label, component in components:
            if _is_terminal_morphism(component):
                continue

            if label != '':
                mors.append((label, component))
            elif not isinstance(component, ProductMor):
                mors.append((label, component))
                if _is_identity(component):
                    self.inplace = True
            else:
                # Flatten. Notice that target will be at least as flat as
                # morphism.
                mors.extend(component.components.items())
                if component.inplace:
                    self.inplace = True

        self.components = ComponentMap(mors)
        super().__init__(source, target)

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, ProductMor)
            and self.components.full_eq(x.components)
        )

    def hint(self):
        return self.components

    def ev(self, x: object):
        def update(dest: dict[object, object], src: object):
            if _isinstance_dict_str_object(src):
                for k, v in src.items():
                    assert k not in res
                    dest[k] = v
            else:
                assert _isinstance_tuple_object(src)
                for k, v in enumerate(src):
                    assert k not in res
                    dest[k] = v

        components = self.components
        if (
            self.inplace
            and _is_product_acceptable(x)
            and isinstance(x, dict)
        ):
            for label, component in components.full_items():
                if label != '':
                    x[label] = component.ev(x)
                else:
                    if _is_identity(component):
                        continue

                    y = component.ev(x)
                    update(x, y)

            return x

        target = self.target
        assert isinstance(target, Product)
        if target.components.tup:
            # Terminal morphism gets handled here.
            dest: list[object] = []
            for label, component in components.full_items():
                if label != '':
                    assert isinstance(label, int)
                    _insert_or_pad(dest, label, component.ev(x))
                else:
                    y = component.ev(x)
                    if _isinstance_dict_str_object(y):
                        for k, v in y.items():
                            assert isinstance(k, int)
                            _insert_or_pad(dest, k, v)
                    else:
                        assert _isinstance_tuple_object(y)
                        for k, v in enumerate(y):
                            _insert_or_pad(dest, k, v)

            return tuple(dest)

        res: dict[object, object] = {}
        for label, component in components.full_items():
            if label != '':
                res[label] = component.ev(x)
            else:
                y = component.ev(x)
                update(res, y)

        return res

    def __repr__(self):
        return f'{type(self).__name__}({self.components})'

# TODO: Review this!
class CartComposition(Composition, CartMor):
    """Handles extra conditions that make two morphisms the same

    The extra condition is the one coming from composition of pairing and
    projection.
    """
    __slots__ = ()

    def exfit(self, source: Obj):
        factors: list[Mor] = []
        for factor in reversed(self.factors):
            factor = factor.exfit(source)
            source = factor.target
            factors.append(factor)

        return source.vcomposition(*reversed(factors))

    @classmethod
    def _simplify_proj(cls, pmor: Mor, mor: Mor) -> Mor | tuple[Mor, Mor]:
        # `pmor` is a morphism with projections such as (f @ a$, g @ b$). When
        # composing with (a=m, b=n), one normalizes to (f @ m, g @ n).
        # Composing with a morphism that is not (extensionally) a pairing
        # cannot lead to normalization, because then the morphism would have to
        # be duplicated. Something like the naturality of the diagonal would
        # still be intensional. Normalization (simplification) gets applied
        # left-associatively. There is no backtracking. Duplication of
        # projections and identities is allowed. This includes composition and
        # pairing of projections, which are actually projections of products of
        # products.

        # First step is to compose with each component of `pmor`. Next step is
        # to simplify each resulting component. Since simplification is applied
        # left-associatively, one only takes the last two factors into account.

        if isinstance(pmor, Composition):
            if pmor.factors:
                # This assumes tail will never be an identity.
                tail, head = pmor.split()
                mm = cls._simplify_proj(head, mor)

                if isinstance(mm, tuple):
                    p, m = mm
                    return tail.compose(p), m

                return tail, mm

            return mor

        return cls._simplify_proj_single_factor(pmor, mor)

    @classmethod
    def _simplify_proj_single_factor(
        cls, pmor: Mor, mor: Mor,
    ) -> Mor | tuple[Mor, Mor]:
        if isinstance(pmor, Projection):
            if isinstance(mor, Projection):
                return pmor.proj_compose(mor)

            if isinstance(mor, ProductMor):
                return mor.after_proj(pmor)

            return pmor, mor

        if _is_terminal_morphism(pmor):
            # No need to handle "expensive" morphisms here, so we deal with
            # terminal morphism as a special case.
            return mor.source.terminal_mor()

        if isinstance(pmor, ProductMor):
            expensive: set[Mor] = set()
            params: list[tuple[str | int, Mor]] = []
            for label, m in pmor.component_compose(mor):
                # If there is a repeated "expensive" morphism, then don't
                # simplify. An "expensive" morphism is one that is not a
                # projection nor a pairing of projections.
                if not cls._extract_expensive_no_repeat(m, expensive):
                    return pmor, mor

                params.append((label, m))

            return mor.source.vproduct_mor(params)

        return pmor, mor

    @classmethod
    def _extract_expensive_no_repeat(cls, mor: Mor, dst: set[Mor]) -> bool:
        # As stated above terminal morphisms get excluded from components.
        if isinstance(mor, Projection):
            return True

        if isinstance(mor, ProductMor):
            return all(
                cls._extract_expensive_no_repeat(m, dst)
                for _, m in mor.components.full_items()
            )

        if mor in dst:
            return False

        dst.add(mor)
        return True

    @classmethod
    def simplify(cls, factors: Sequence[Mor]):
        factor_it = iter(super().simplify(factors))
        for prev in factor_it:
            break
        else:
            return ()

        _factors: list[Mor] = []
        for factor in factor_it:
            # The resulting morphism (or first morphism) will have the same
            # target as `prev`.
            mm = cls._simplify_proj(prev, factor)
            if isinstance(mm, tuple):
                p, prev = mm
                _factors.append(p)
            else:
                prev = mm
        _factors.append(prev)

        return _factors

CartObj.init_cls()
