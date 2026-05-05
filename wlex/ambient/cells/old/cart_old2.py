"""Cart cell classes"""
from typing import Self, TypeGuard, override, Union
from collections.abc import Sequence, MutableSequence, Generator
from abc import ABCMeta

from ..cells import Obj, Mor, Eq, PrimMor
from .category import (
    CategoryObj, CategoryMor, CategoryEq, CategoryPrimEq, Composition,
)

class CartObj(CategoryObj, metaclass=ABCMeta):
    """Models object `cart.Obj`"""
    __slots__ = ()

    _product_cls: type['Product']
    _product_mor_cls: type['ProductMor']

    @classmethod
    def init_cls(cls):
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
        params: Sequence['LabeledObj'],
        no_repeat: bool = False,
    ):
        return cls._product_cls(params, no_repeat=no_repeat)

    @override
    def vproduct_mor(
        self,
        params: Sequence['LabeledMor'],
    ) -> Mor:
        return self._product_mor_cls(self, params)

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
        eq = Eq(p.pairing(q), mor)
        eq.proven = True
        return eq

class CartPrimMor(PrimMor, CartMor, metaclass=ABCMeta):
    """Models object `cart.Mor` as primitive"""
    __slots__ = ()

CartEq = CategoryEq
CartPrimEq = CategoryPrimEq

Label = str | tuple[str, ...]
LabeledObj = tuple[Label, Obj]
LabeledMor = tuple[Label, Mor]
ProjTree = list[tuple[Label, Union[tuple[int, ...], 'ProjTree']]]
ComponentTree = Generator[tuple[Label, Union[Obj, 'ComponentTree']]]

class Product(CartObj):
    """Models object corresponding to source of span `cart.product`"""
    # Concretely, a product is a mapping of indices to types, along with
    # optional names for composed projections. In extensive categories products
    # can be understood as internal homsets (one just needs all finite sets) or
    # dependent products. If component has name, using the index will keep the
    # name, as if the type was a single component product. In fact single
    # component product does not support indexing. There is no restriction on
    # how components can be labeled with respect to their indices, however this
    # may affect the ability to match componenents with labels, since labeling
    # has several purposes.

    # Single component products are actually just the component type with a
    # label. There must always be a label. Index access is not supported in
    # this case. It makes sense then to keep labels when accessing through
    # indices (target of projection must be single component product).

    # Components can be matched through their types (even if the types are
    # anonymous, such as products). Matching components is required for
    # determining that two types are the same, or determining an isomorphism
    # between them. When using both indices and labels for matching components,
    # once labels are used for matching, one first tries to match using indices.??
    # If matching is completed solely through indices then the products are
    # identical (they are the same mapping, they have the same instances, etc.).
    # Matching through indices does not apply if the source component has a label
    # and this label differs from the target label.
    # Labels (and types) are used for matching when determining an isomorphism,
    # when index matching fails. After the first component that is matched
    # through this method, all other components must be matched through this
    # method as well.

    # Source components that get matched to target components (one label for both
    # target components) must have the same label!

    # Indentity requires the same labels for the same index projections (or
    # composite projections). This is specially important in the case of
    # products with overlapping label. To simplify manipulation of instances
    # and their types, all components of the product components are kept. *One
    # should in fact be able to determine inclusion morphisms as with any
    # pullback.* However determining "expander" morphisms (pairing of identities
    # and diagonals) must be done manually.

    # Labels one depth level down are not overridden with tuple labels.
    # Sameness and accepting of instances can only be based on indices.
    # Instances of a single component product must be the instances of the
    # component type, which can itself be a product. This means that for
    # simplicity it is better to avoid single item tuples as instances of
    # any type.

    # Types as labels is only allowed when there is the type corresponds only
    # to one component regardless of this component being labeled.

    # An isomorphism conversion is introduced regardless of labels when there
    # is only one component of each type, or when index/label(/type) matching
    # succeeds. One tries matching indices first, then label/types.

    __slots__ = 'components', 'labels'

    components: list[LabeledObj]
    labels: dict[str | Obj, tuple[int, ...]] # Maps to the first index with label

    def _tree_to_proj_pairing(self, tree: ProjTree) -> Mor:
        params: list[LabeledMor] = []

        for node in tree:
            if node is None:
                raise ValueError("Found empty node in tree")

            label, idx = node
            if isinstance(idx, tuple):
                mor = Projection.from_path(self, idx)
            else:
                mor = self._tree_to_proj_pairing(idx)

            params.append((label, mor))

        return self.vproduct_mor(params)

    def conversion(self, obj: Obj):
        # TODO: There must be a conversion from any object to single component products
        # (which handles also the case when the object is itself a product).
        # conversion is an isomorphism.

        # Pullback isomorphisms (diagonals) require (str) label matching, unless
        # the labels are repeated in both `self` and `obj` and they appear in
        # the same positions.

        def tree_insert(
            t: ProjTree,
            l: tuple[Label, ...],
            src: tuple[int, ...],
            tgt: tuple[int, ...],
            offset: int = 0,
        ):
            idx = tgt[offset]
            lbl = l[offset]
            if idx >= len(t):
                t.extend(None for _ in range(len(t) - idx))

            if len(tgt) - offset == 1:
                if idx >= len(t):
                    t.append((lbl, src))
                elif t[idx] is None:
                    t[idx] = (lbl, src)
                else:
                    assert False

                return

            s: ProjTree = []
            if idx >= len(t):
                t.append((lbl, s))
            elif t[idx] is None:
                t[idx] = (lbl, s)
            else:
                assert False

            tree_insert(s, l, src, tgt, offset=offset+1)


        res = super().conversion(obj)
        if res is not None:
            return res

        if len(self.components) == 1 and self.components[0][1].identical(obj):
            return self.iproj(-1)

        if not isinstance(obj, Product):
            return None

        tree: ProjTree = []
        used_labels: set[str] = set()
        prev_m: Label | None = None
        prev_t: Obj | None = None
        params: list[LabeledMor] = []

        # SIMPLIFY LABELING! What would ((x, y): T) be?
        # ALTERNATIVE: No flattening (easy handling of subobj comps), but
        #
        # Index matching
        t_it = iter(obj.components)
        for i, ((l, s), (m, t)) in enumerate(zip(self.components, t_it)):
            conv = s.conversion(t)
            if conv:
                if not l and m:
                    if not isinstance(m, tuple):
                        m = (m,)

                    for ml in m:
                        if ml in used_labels:
                            # No matching is possible in this case.
                            return None

                        used_labels.add(ml)
                elif l != m and not (
                    s in self.labels
                    and t in obj.labels
                ):
                    prev_m = m
                    prev_t = t
                    break

                # The projection index (source index) coincides with the
                # component index (target index).
                params.append((m, conv.compose(self.iproj(i))))
        else:
            if len(self.components) == len(obj.components):
                mor = self.vproduct_mor(params)
                assert mor.target.identical(obj)
                return mor

            # One should be able to handle this cases outside this `else` within
            # the regular process of matching labels.

            #if len(self.components) < len(obj.components):
                # In this case all remaining components in `obj` must have (str)
                # labels from the ones that have already appeared. We append a
                # projection for each such label to obtain the (fake) diagonals.
                # used labels means all labels that have so far appeared in `obj`.
                # The labels required for the diagonals must also have appeared in `self`
                # in order to allow label matching.
            #    pass

            #if len(self.components) > len(obj.components):
                # Same as before. Only one projections. used labels means all labels that have so far appeared in `self`.
            #    pass

        # We traverse `obj.components`, since resulting morphism will have this
        # shape (`obj` is the target).
        if prev_m is not None:
            pass

        # TODO: We must still make sure that all remaining labels (str of type) in `self` get used!

        for m, t in t_it:
            # If the type is unique among components, then it does not matter
            # that the (str) labels don't match.
            if not m:
                if t in self.labels:
                    params.append((m, self.proj(t)))
                else:
                    return None
            elif isinstance(m, str):
                if m in self.labels:
                    params.append((m, self.proj(m)))
                elif t in self.labels:
                    params.append((m, self.proj(t)))
                else:
                    return None
            else:
                # In this case we must also set the labels of the product component!
                assert isinstance(t, Product)

                # Missing labels in the tuple must correspond to type labels in
                # `obj`.
                for _, l, c in t.labels_to_indices(m):
                    if not l and c not in obj.labels:
                        return None

                p = self.wproj(t)
                if p is None:
                    return None

                params.append((m, p))

        # All type/labels in `self` must appear in `obj`.
        # If a component type appears once in `self` then it also appears once
        # in `obj`, so that in both cases the type appears in labels.

        for label, s_idx in self.labels.items():
            t_idx = obj.labels[label]
            for i in t_idx:
                # Handle repeated indices by skipping them
                params

        # All labels in `obj` except the ones in `used_labels` must appear in
        # `self`.
        for label in obj.labels:
            if label in used_labels:
                continue

            assert label in self.labels

        # TODO: Assert that the target is obj


    def iproj(self, idx: int):
        if idx < 0:
            if len(self.components) != 1:
                raise ValueError("Index -1 requires single component product")

            return Projection(self, self.components[0][1], (-1,))

        # We don't use [*, A] ~= A here when having single component, because of
        # the inability to decide at what level should a 0 index be applied.
        return Projection.from_path(self, (idx,))

    @override
    def proj(self, label: str | Obj):
        return Projection.from_path(
            self, self.index_to_projection_path(self.labels[label]),
        )

    def get_component(self, idx: int) -> LabeledObj:
        if idx < 0:
            if len(self.components) != 1:
                raise ValueError("Index -1 requires single component product")

            return '', self.components[0][1]

        obj = self
        while len(obj.components) == 1:
            obj = self.components[0]

            if not isinstance(obj, Product):
                raise ValueError("Index requires product component.")

        return obj.components[idx]

    def flat_length(self):
        """Length of product including the length of subproducts"""
        return len(self.components) + sum(
            len(l) - 1 for l, _ in self.components
            if isinstance(l, tuple)
        )

    def flat_enumerate(self) -> Generator[tuple[tuple[int, ...], str, Obj]]:
        for idx, (label, component) in enumerate(self.components):
            if isinstance(label, tuple):
                assert isinstance(component, Product)
                for l, (i, _, c) in zip(label, component.flat_enumerate()):
                    yield (idx, *i), l, c
            else:
                yield (idx,), label, component

    def wproj(self, t: 'Product', labels: tuple[str, ...]) -> Mor | None:
        # `t` is the target.
        params: list[LabeledMor] = []

        # If only one of source and target has tuple label?

        for label, c in t.tree():
            if isinstance(c, Obj):
                pass


    def wproj2(self, t: Product) -> Generator[tuple[tuple[int, ...], str, Obj]]:
        for idx, (label, component) in enumerate(self.components):
            if isinstance(label, tuple):
                assert isinstance(component, Product)
                for l, (i, _, c) in zip(label, component.flat_enumerate()):
                    yield (idx, *i), l, c
            else:
                yield (idx,), label, component

    def labels_to_indices(
        self, labels: Sequence[str],
    ) -> Generator[tuple[tuple[int, ...], str, Obj]]:
        if not labels:
            labels = ['' for _ in range(self.flat_length())]

        if len(labels) != self.flat_length():
            raise ValueError(
                "Tuple of names must have the flat length of product as "
                "length.",
            )

        for label, (idx, orig_label, component) in zip(
            labels, self.flat_enumerate(),
        ):
            yield idx, label or orig_label, component

    def tree(self) -> ComponentTree:
        for label, component in self.components:
            if isinstance(label, tuple):
                assert isinstance(component, Product)
                yield label, component.tree()
            else:
                yield label, component

    def index_to_component(
        self, index: tuple[int, ...], _offset: int = 0,
    ) -> LabeledObj:
        # Low level: This allows index on single component product
        component = self.components[index[_offset]]
        if len(index) - _offset == 1:
            return component
        assert isinstance(component, Product)
        return component.index_to_component(index, _offset=_offset+1)

    def label_to_index_component(self, label: str | Obj):
        # There is no point in trying label on deeper levels when length of
        # components is 1.
        idx = self.labels[label]
        return idx, self.index_to_component(idx)[1]

    def index_to_projection_path(self, idx: tuple[int, ...]):
        obj = self
        res: list[int] = []
        for i in idx:
            assert isinstance(obj, Product)
            if len(obj.components) == 1:
                assert i == 0
                res.append(-1)
            else:
                while res and res[-1] == -1:
                    res.pop()

                res.append(i)

            _, obj = obj.components[i]

        return tuple(res)

    def _add_labels(
        self, labels: tuple[str, ...],
        obj: 'Product', excluded_types: set[Obj],
        root_idx: int, no_repeat: bool,
    ) -> tuple[str, ...]:
        # We can't allow repeated label in the filled `labels` because this
        # would change the type of the product component.
        used_labels: set[str] = set()
        new_labels: list[str] = []
        for idx, label, component in obj.labels_to_indices(labels):
            new_labels.append(label)
            if label:
                if label in used_labels:
                    raise ValueError(
                        "Repeated label for product component is not allowed."
                    )

                used_labels.add(label)

                if label in self.labels:
                    if no_repeat:
                        raise ValueError(
                            "Repeated label not allowed"
                        )

                    _, c = self.label_to_index_component(label)

                    if not c.identical(component):
                        raise ValueError(
                            "Repeated label requires repeated associated "
                            "product component.",
                        )
                else:
                    self.labels[label] = (root_idx, *idx)

        for label in obj.labels:
            if isinstance(label, Obj):
                if label in excluded_types:
                    pass
                elif label in self.labels:
                    # We remove the type label only if it appears with a
                    # different (str) label (or no label at all).
                    idx = self.labels[label]
                    oidx = obj.labels[label]
                    l, typ = self.index_to_component(idx)
                    ol, otyp = obj.index_to_component(oidx)
                    assert label is otyp
                    assert otyp.identical(typ)
                    if l != ol:
                        excluded_types.add(label)
                        del self.labels[label]
                else:
                    self.labels[label] = (root_idx, *obj.labels[label])

        return tuple(new_labels)

    def _add_component(
        self, label: Label,
        obj: Obj, excluded_types: set[Obj],
        no_repeat: bool,
    ):
        # TODO: A product such as ((l: a), b) has to be distinguished from (l: a, b),
        # because of the way the target of th pairing is determined:
        # (f, g), (l: f, g), ((l: f), g). One way to avoid this is to always delabel
        # single component target morphisms when initializing pairings by precomposing
        # with the delabeling proj.
        root_idx = len(self.components)

        if not label and isinstance(obj, Product) and len(obj.components) == 1:
            label, obj = obj.components[0]

        if isinstance(label, tuple):
            if not isinstance(obj, Product):
                raise TypeError(
                    "An object associated to a tuple of names must be an "
                    "instance of `Product`.",
                )

            label = self._add_labels(label, obj, excluded_types, root_idx, no_repeat)
        elif label:
            if label in self.labels:
                if no_repeat:
                    raise ValueError(
                        "Repeated label not allowed"
                    )

                _, component = self.label_to_index_component(label)

                if not component.identical(obj):
                    raise ValueError(
                        "Repeated label requires repeated associated object.",
                    )
            else:
                self.labels[label] = (root_idx,)

        # This will for example add product type as label even if it is "flat".
        if obj in excluded_types:
            pass
        elif obj in self.labels:
            # We remove the type label only if it appears with a different (str)
            # label (or no label at all).
            idx = self.labels[obj]
            l, typ = self.index_to_component(idx)
            assert obj.identical(typ)
            if l != label:
                excluded_types.add(obj)
                del self.labels[obj]
        else:
            self.labels[obj] = (root_idx,)

        self.components.append((label, obj))

    def __new__(cls, components: Sequence[LabeledObj], no_repeat: bool = False):
        if not components:
            terminal = getattr(cls, '_terminal', None)
            if isinstance(terminal, cls):
                return terminal

            cls._terminal = super().__new__(cls)

        return super().__new__(cls)

    def __init__(self, components: Sequence[LabeledObj], no_repeat: bool = False):
        # Repeated component labels are allowed. This is based on the fact that
        # AxBxC is the pullback of the projections AxB->B and BxC->B.

        # Avoid reinitializing terminal object
        if (
            not components and self is self._terminal
            and hasattr(self, 'components')
        ):
            return

        if len(components) == 1:
            label, _ = components[0]
            if not label:
                raise ValueError("Can't have single component without label")

        self.components = []
        self.labels = {}
        excluded_types: set[Obj] = set()

        for component in components:
            self._add_component(*component, excluded_types, no_repeat)

    def identical(self, x: Obj):
        # In order to be consistent with `accepts` and `same`, two objects can
        # only be identical if they the have the same components with the same
        # labels in the same order.
        return super().identical(x) or (
            isinstance(x, Product)
            and len(self.components) == len(x.components)
            and all(
                n == m and s.identical(t)
                for (n, s), (m, t)
                in zip(self.components, x.components)
            )
        )

    def hint(self):
        return self.components

    def accepts(self, x: object):
        if len(self.components) == 1:
            return self.components[0][1].accepts(x)

        # TODO: This doesn't take into account repeated labels!
        if _isinstance_sequence_object(x):
            if len(x) != len(self.components):
                return False

            return all(
                obj.accepts(x[i])
                for i, (_, obj) in enumerate(self.components)
            )

        return False

    def same(self, x: object, y: object):
        if len(self.components) == 1:
            return self.components[0][1].same(x, y)

        if _isinstance_sequence_object(x):
            if _isinstance_sequence_object(y):
                if len(x) == len(y):
                    return all(
                        obj.same(p, q)
                        for (_, obj), p, q in zip(self.components, x, y)
                    )

                return False

            return False

        raise TypeError("Expected sequences")

    def __str__(self):
        name = super().__str__()
        if name is NotImplemented:
            components = (
                f'{n}: {t}'
                for n, t in self.components
            )
            return f'({', '.join(components)})'
        return name

    def __repr__(self):
        return f'`product {self!s}`'

def _isinstance_sequence_object(x: object) -> TypeGuard[Sequence[object]]:
    return isinstance(x, Sequence)

def _isinstance_mutable_sequence_object(x: object) -> TypeGuard[MutableSequence[object]]:
    return isinstance(x, MutableSequence)

def _is_identity(mor: Mor):
    # Identity in an extensional sense
    return isinstance(mor, Composition) and mor.factors == ()

class Projection(CartMor):
    "Models morphism corresponding to projection"
    __slots__ = ('path',)

    def __init__(
            self, source: Product, target: Obj, path: tuple[int, ...],
        ):
        # Instantiation occurs by calling `source.proj`, which takes care of
        # checking `path` and preprocessing it (cnverting it to ints).

        # Index -1 means removing the label in single component product.
        # There is no point in having -1 before positive indices.

        self.path = path
        super().__init__(source, target)

    @classmethod
    def from_path(cls, source: Product, path: Sequence[int | str | Obj]):
        """Create projection from path"""
        # `path` names must be a key of `components`.
        target = source
        idx_path: list[int] = []

        tlabel = ''
        for label in path:
            if isinstance(target, Product):
                if isinstance(label, int):
                    # `label` can be negative.
                    idx = label
                    tlabel, target = target.get_component(idx)
                else:
                    if tlabel:
                        # In this case label must coincide with tlabel so as to
                        # apply delabeling of (implicit) product with target as
                        # single component.
                        assert label == tlabel
                        idx = -1
                    else:
                        idx, t = target.label_to_index_component(label)
                        idx = target.index_to_projection_path(idx)
                        target = t
                        if idx[-1] >= 0:
                            idx = (*idx, -1)

                    tlabel = ''
            else:
                raise ValueError(
                    "name in `path` does not correspond to `Product` component"
                    "as expected."
                )

            if (
                isinstance(idx, tuple)
                and idx and idx[0] >= 0
            ) or (isinstance(idx, int) and idx >= 0):
                # Remove superfluous -1
                while idx_path and idx_path[-1] < 0:
                    idx_path.pop()

            if isinstance(idx, tuple):
                idx_path.extend(idx)
            else:
                idx_path.append(idx)

        if target is source:
            raise ValueError("Empty `path`")

        if tlabel:
            target = Product(((tlabel, target),))

        return cls(source, target, tuple(idx_path))

    def proj_compose(self, mor: Self):
        """Compose with projections into a single projection"""
        source = mor.source
        target = self.target
        assert isinstance(source, Product)

        if self.path[0] < 0:
            return Projection(source, target, (*mor.path, *self.path))

        mpath = list(mor.path)
        while mpath and mpath[-1] < 0:
            mpath.pop()

        return Projection(source, target, (*mpath, *self.path))

    def ev(self, x: object):
        # `x` beieng accepted by source (as can be checked in `self.public_ev`)
        # is proof enough that the result of `self.ev` is accepted by `target`.
        # The point of defensive evaluation is to check that the target accepts
        # the result when this is not guaranteed by having the source accept the
        # argument.
        for idx in self.path:
            if idx >= 0:
                assert _isinstance_sequence_object(x)
                assert len(x) > 1
                x = x[idx]
            else:
                break

        return x

    def same(self, x: Mor):
        if super().same(x):
            return True

        return (
            isinstance(x, Projection)
            and self.path == x.path
            and self.source.identical(x.source)
        )

    def hint(self):
        return self.path, self.source

    def __str__(self):
        name = super().__str__()
        if name is NotImplemented:
            return ' '.join(
                f'{n}$' for n in self.path
            )
        return name

    def __repr__(self):
        return f'`proj {self!s}[{self.source}]`'

class ProductMor(CartMor):
    """Models object corresponding to `cart.ProductMor`"""
    __slots__ = ('components',)

    # The names are in the target.
    components: list[Mor]

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
        for i, idx in enumerate(mor.path):
            if idx >= 0:
                while isinstance(res, ProductMor) and len(res.components) == 1:
                    res = res.components[0]

            if isinstance(res, ProductMor):
                if idx < 0:
                    assert len(res.components) == 1
                    res = res.components[0]
                else:
                    res = res.components[idx]

                continue

            # The returned projection is truncated to include all remaining
            # indices with the target of `res` as its source.
            t = res.target
            assert isinstance(t, Product)
            return Projection.from_path(t, mor.path[i:]), res

        return res

    def component_compose(self, mor: Mor):
        """Compose each component with `mor`"""
        target = self.target
        assert isinstance(target, Product)

        for (label, _), m in zip(target.components, self.components):
            res = m.compose(mor)
            yield label, res

    def __init__(self, source: Obj, components: Sequence[LabeledMor]):
        if len(components) == 1:
            label, _ = components[0]
            if not label:
                raise ValueError("Can't have single component without label")

        self.components = []
        target_params: list[LabeledObj] = []

        for label, c in components:
            target = c.target

            # Merge single component product target
            if not label and isinstance(target, Product) and len(target.components) == 1:
                c = target.iproj(-1).compose(c)

            self.components.append(c)
            target_params.append((label, target))

        target = source.vproduct(target_params, no_repeat=True)
        super().__init__(source, target)

    def same(self, x: Mor):
        return super().same(x) or (
            isinstance(x, ProductMor)
            and self.target.identical(x.target)
            and len(self.components) == len(x.components)
            and all(
                s.same(t)
                for s, t
                in zip(self.components, x.components)
            )
        )

    def hint(self):
        return self.target, self.components

    def ev(self, x: object):
        # In the case of the local namespace (regarded as Product instance)
        # there is a special composition that makes sure that linearity is
        # respected.
        components = self.components
        length = len(components)
        if length == 1:
            return components[0].ev(x)

        if length > 1:
            first = components[0]
            if _is_identity(first) and _isinstance_mutable_sequence_object(x):
                # `first` is the local namespace and the remaining components
                # are the assignments.
                x.extend(components[i].ev(x) for i in range(1, len(components)))
                return x

        return tuple(c.ev(x) for c in components)

class CartComposition(Composition, CartMor):
    """Handles extra conditions that make two morphisms the same

    The extra condition is the one coming from composition of pairing and
    projection.
    """
    __slots__ = ()

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

        if isinstance(pmor, ProductMor):
            expensive: set[Mor] = set()
            params: list[LabeledMor] = []
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
                for m in mor.components
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
