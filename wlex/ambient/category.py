"""High level interface to category ambient"""
from collections.abc import Callable, Iterator, Sequence
from abc import ABCMeta, abstractmethod
from typing import Any, Self, TypeGuard, TypeVar, overload
from itertools import chain

from .cells import Obj, Mor, Eq, MorStub, EqStub, PrimEv, PrimEq, Axiom
from .cells.category import Composition
from . import cells
from .public import category as public

Transformation = Callable[[Obj], Mor]
MorLike = Mor | Obj | Transformation
EqLike = MorLike | Eq
Prover = Callable[[Mor, Mor], Eq]

class UnprovenEq(Exception):
    pass

# def _fit_mor(source: Obj, target: Obj, cell: Mor):
#     # Subclasses of `Obj` can support specific type conversions. Handling of
#     # transformations occurs before this (in which case no fitting is
#     # needed).
#     sconv = source.trim(cell.source)
#     if not sconv:
#         raise cells.SourceUnfit("Can't convert", source, cell.source)

#     tconv = cell.target.trim(target)
#     if not tconv:
#         raise cells.TargetUnfit("Can't convert", cell.target, target)

#     # This will be just `cell` when `tconv` as `sconv` are identities.
#     return tconv.compose(cell).compose(sconv)

def check_signature(source: Obj, target: Obj, cell: Mor):
    if not source.identical(cell.source):
        raise cells.SourceUnfit("Wrong source", source, cell.source)

    if not target.identical(cell.target):
        raise cells.TargetUnfit("Wrong target", cell.target, target)

def _source_fit_mor_like(source: Obj, cell: MorLike):
    if isinstance(cell, Callable):
        cell = cell(source)

    if isinstance(cell, Obj):
        cell = cell.identity()

    sconv = source.trim(cell.source)
    if not sconv:
        raise cells.SourceUnfit(
            "Can't convert for fitting source", source, cell.source,
        )

    #return cell.compose(sconv)
    return cell, sconv

def _source_fit_eq(source: Obj, cell: Eq):
    sconv = source.trim(cell.ssource.source)
    if not sconv:
        raise cells.SourceUnfit(
            "Can't convert for fitting source", source, cell.ssource.source,
        )

    #return cell.compose_eq(sconv.ref())
    return cell, sconv.ref()


def _ssource_fit_eq(ssource: Mor, cell: Eq, prove: Prover):
    # TODO: This seems wrong. It be better to not do any "fitting" here of
    # morphism. Also since the conversion is not guaranteed to match
    # (calls to fit for lifitng may be needed), one must return a tuple
    # of cells instead of composing.
    #cell = _target_fit_eq(ssource.source, cell)

    sconv = prove(ssource, cell.ssource)
    # TODO: Check that trans is not relying on implicit symmetry. This would be too messy!

    if not sconv:
        raise cells.SSourceUnfit(
            "Can't convert for fitting setoid source",
            ssource, cell.ssource,
        )

    return cell.trans(sconv)

# def _target_fit_eq(target: Obj, cell: Eq):
#     tconv = cell.ssource.target.trim(target)
#     if not tconv:
#         raise cells.TargetUnfit(
#             "Can't convert for fitting target", cell.ssource.target, target,
#         )

#     return tconv.ref().compose_eq(cell)

# def _fit_eq(ssource: Mor, starget: Mor, cell: Eq, prove: Prover):
#     prev_err = None
#     for i in range(2):
#         try:
#             sconv = prove(ssource, cell.ssource)
#             if not sconv:
#                 raise cells.SSourceUnfit("Can't convert", ssource, cell.ssource)

#             tconv = prove(cell.starget, starget)
#             if not tconv:
#                 raise cells.STargetUnfit("Can't convert", cell.starget, starget)
#         except cells.MorUnfit as err:
#             if i == 0:
#                 # Use of `sym` is justified here, because it doesn't get
#                 # handled by `prove`.
#                 cell = cell.sym()
#                 prev_err = err
#                 continue

#             raise err from prev_err

#         return tconv.trans(cell).trans(sconv)

#     assert False

def _mor_like_to_mor_ssignature(ssignature: tuple[MorLike, MorLike]):
    ssource, starget = ssignature
    ssource, starget = (
        m.identity() if isinstance(m, Obj) else m
        for m in (ssource, starget)
    )

    if isinstance(ssource, Mor):
        if not isinstance(starget, Mor):
            starget = starget(ssource.source)
    elif isinstance(starget, Mor):
        ssource = ssource(starget.source)
    else:
        raise TypeError(
            "At least one of `ssource` and `starget` must be a morphism.",
        )

    return ssource, starget

# def _is_proven_eq(
#     proven_eqs: set[tuple[Mor, Mor]],
#     ssource: Mor, starget: Mor,
# ) -> bool:
#     if (ssource, starget) in proven_eqs or (starget, ssource) in proven_eqs:
#         return True

#     return False

    # Handling all possible ways in which an equality can arise would be
    # unfeasible. Composition split based equalities are useful for liftings.
    # TODO: Are they?
    # TODO: Provide instead the specific equality! Move this to `def _prove`.
    # try:
    #     tail_s, head_s = ssource.split()
    #     tail_t, head_t = starget.split()
    #     return (
    #         _is_proven_eq(proven_eqs, tail_s, tail_t)
    #         and _is_proven_eq(proven_eqs, head_s, head_t)
    #     )
    # except (ValueError, TypeError):
    #     return False

def one[T](*args: T | None) -> T:
    """Returns the unique argument that is not None"""
    res: T | None = None
    for a in args:
        if a is not None:
            if res is None:
                res = a
            elif res is not a:
                if isinstance(res, TheoryStub):
                    res = res.with_base(a)
                else:
                    raise ValueError("More than one value was provided.")

    if res is None:
        raise ValueError("No value was provided.")

    return res

class TheoryStub(metaclass=ABCMeta):
    """Base class for the theory stub"""

    @abstractmethod
    def with_base(self, base: Any) -> Self:
        """Combine `self` and `base`"""

    @abstractmethod
    @classmethod
    def from_theory(cls, theory: Any) -> Self:
        """Create stub from theory"""

class Theory(metaclass=ABCMeta):
    """Base class for theories"""

    Stub: type[TheoryStub]

    @abstractmethod
    @classmethod
    def from_prim(cls, ctx: Any, prim: Any) -> Self:
        """Create theory from primitives"""
        # Some rules must be followed in the implementation, which are not
        # enforced through code. Attributes of `prim` must be used exactly once
        # to define variables of the same name. These variables must then be
        # used instead of accessing the attributes.
        # TODO: primitives can't be changed through conversion
        #       (including Obj -> Mor thorugh identity, etc.)!
        # TODO: primitives shouldn't be used (e.g. in composition, identity, etc.)
        #       before being named.

    @classmethod
    def is_own_stub(cls, stub: TheoryStub):
        """Stub corresponds to theory"""
        return isinstance(stub, cls.Stub)

class Context:
    """Handles cells of a theory with ambient category"""
    __slots__ = 'name_stack', 'proven_eqs'
    name_stack: tuple[str, ...]
    proven_eqs: set[tuple[Mor, Mor]] # set of ssignatures

    compose = staticmethod(public.compose)
    compose_eq = staticmethod(public.compose_eq)
    trans = staticmethod(public.trans)
    sym = staticmethod(public.sym)
    identity = staticmethod(public.identity)
    ref = staticmethod(public.ref)
    #from wlex.ambient.public import category # TODO: This should be variable!
    # Have a Category class with all the backend functions, etc.?
    # ABC interface would be overkill, just use a dataclass with Callable attributes, etc.
    # The objects of category are Obj, Mor, Eq, which would be essentially hardcoded.
    # This isn't a problem as long as the accept method of backend.Obj is
    # isinstance(x, Obj), etc. Include only the actually publicly used cells of category.
    # The problem of using dataclass is that one ends up having to repeat all the function signatures.

    def __init__(self, proven_eqs: set[tuple[Mor, Mor]] | None = None):
        self.name_stack = ()
        if proven_eqs is None:
            self.proven_eqs = set()
        else:
            self.proven_eqs = proven_eqs

    @property
    def id(self):
        """`public.identity` as `Transformation`"""
        return self.identity

    def with_name(self, name: str):
        """Shallow copy of `self` with name added to its `name_stack`"""
        ctx = Context(proven_eqs=self.proven_eqs)
        ctx.name_stack = (*self.name_stack, name)
        return ctx

    def sub[S: TheoryStub, T: Theory](
        self, name: str, theory: type[T], prim: S,
        base: S | None = None,
    ):
        """Sets name on subtheory"""
        # Pylance type checking does not catch this!
        if not theory.is_own_stub(prim):
            raise TypeError("Wrong stub class")

        if base:
            prim = prim.with_base(base)def sub

        # There is checking for keeping attributes of `prim` from remaining
        # unused. Also, checking that the resulting theory has no empty
        # attributes.
        # TODO: Check that context arg is of the right type!
        return theory.from_prim(self.with_name(name), prim)

    def _set_name(self, name: str, cell: cells.Cell):
        # An empty `name` may occur in the case of equalities.
        if not (hasattr(cell, 'name') and cell.name[-1]):
            cell.name = (*self.name_stack, name)

    def obj(self, name: str, cell: Obj):
        """Sets name on object"""
        self._set_name(name, cell)
        return cell

    @overload
    def mor(
        self, name: str, cell: MorLike | MorStub,
        signature: tuple[Obj, Obj],
    ) -> Mor: ...
    @overload
    def mor(
        self, name: str, cell: MorLike | MorStub,
        signature: tuple[Obj, Mor | Transformation],
    ) -> tuple[Mor, Callable[[EqLike | EqStub | None], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: MorLike | MorStub,
        signature: tuple[Mor | Transformation, Mor | Transformation],
    ) -> tuple[Mor, Callable[[EqLike | EqStub | None], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: MorLike | MorStub,
        signature: tuple[Obj, Obj, Obj, Mor | Transformation],
    ) -> tuple[Mor, Callable[[EqLike | EqStub | None], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: MorLike | MorStub,
        signature: tuple[Obj, Obj, Mor | Transformation, Mor | Transformation],
    ) -> tuple[Mor, Callable[[EqLike | EqStub | None], Eq]]: ...
    @overload
    def mor(
        self, name: str, cell: Obj | MorStub,
        signature: None = None,
    ) -> Mor: ...

    def mor(
        self, name: str, cell: MorLike | MorStub,
        signature: tuple[MorLike, MorLike] | tuple[Obj, Obj, MorLike, MorLike] | None = None,
    ):
        """Sets name on morphism and checks signature"""
        final_source: Obj | None = None
        final_target: Obj | None = None
        if signature and len(signature) == 4:
            final_source, final_target, s_s, s_t = signature

            if isinstance(s_s, Callable):
                s_s = s_s(final_source)

            if isinstance(s_t, Callable):
                s_t = s_t(final_target)

            signature = s_s, s_t

        # Object `target` is disallowed here, because it would have the same
        # effect as setting the value of the morphism being created to
        # `source`. There must preferably be only one way to do things.
        if isinstance(cell, Obj):
            cell = cell.identity()

        if not signature:
            # Here `cell` can't be a transformation. A composition with
            # transformations can only be checked after providing a source.
            # For this and other reasons, it makes sense to not make
            # transformation part of the theory the way morphisms are.
            # This convers callable `MorStub`.
            if isinstance(cell, (Callable, PrimEv)):
                raise TypeError(
                    "If `cell` is callable, signature is needed.",
                )

            self._set_name(name, cell)
            return cell

        source, target = signature
        if isinstance(source, Obj):
            if isinstance(cell, Callable):
                # There is no assumption about source being preserved here.
                cell = cell(source)

            if isinstance(target, Obj):
                if isinstance(cell, PrimEv):
                    cell = cell.to_mor(source, target)

                #cell = _fit_mor(source, target, cell)
                cell = self.c(target, cell, source)
                check_signature(source, target, cell)
                self._set_name(name, cell)
                return cell

            if isinstance(target, Callable):
                if isinstance(cell, PrimEv):
                    raise TypeError( # hat morphism
                        "Callable `MorStub` can't have transformation as "
                        "target.",
                    )

                target = target(cell.target)
            elif isinstance(cell, PrimEv):
                cell = cell.to_mor(source, target.source)

            if final_source:
                assert final_target
                check_signature(final_source, final_target, cell)

            return self._hat_mor(
                name, cell, (source, target.source),
                (source.identity(), target),
            )

        if isinstance(cell, Callable):
            if isinstance(source, Callable):
                raise TypeError(
                    "Can't have both `cell` and `source` of type "
                    "`Transformation`",
                )

            cell = cell(source.source)

        if isinstance(source, Callable):
            if isinstance(cell, PrimEv):
                raise TypeError(
                    "Callable `MorStub` can't have transformation as "
                    "source.",
                )

            source = source(cell.source)

        if isinstance(target, Callable):
            if isinstance(cell, PrimEv):
                raise TypeError(
                    "Callable `MorStub` can't have transformation as "
                    "target.",
                )

            target = target(cell.target)

        assert not isinstance(target, Obj)
        if isinstance(cell, PrimEv):
            cell = cell.to_mor(source.source, target.source)

        if final_source:
            assert final_target
            check_signature(final_source, final_target, cell)

        return self._hat_mor(
            name, cell, (source.source, target.source), (source, target),
        )

    def _hat_mor(
        self, name: str, cell: Mor,
        signature: tuple[Obj, Obj], hat_signature: tuple[Mor, Mor],
    ) -> tuple[Mor, Callable[[EqLike | EqStub | None], Eq]]:
        """Sets name on morphism and checks signature"""
        source, target = signature
        #cell = _fit_mor(source, target, cell)
        cell = self.c(target, cell, source)
        hat_source, hat_target = hat_signature

        def _hat(c: EqLike | EqStub | None):
            # We defer assigning hat, because we may end up needing cell in its
            # definition.
            return self.eq(
                c, (hat_source, hat_target.compose(cell)),
            )

        self._set_name(name, cell)
        return cell, _hat

    # def _prove(self, ssource: Mor, starget: Mor):
    #     if (ssource, starget) in self.proven_eqs:
    #         e = Eq(ssource, starget)
    #         e.proven = True
    #         return e

    #     return None

    def prove(self, ssource: Mor, starget: Mor, _fork: bool = True) -> Eq:
        # Reflexivity
        if ssource.same(starget):
            return self.ref(ssource)

        e = Eq(ssource, starget)
        e.proven = True
        if (ssource, starget) in self.proven_eqs:
            return e

        # Symmetry
        if (starget, ssource) in self.proven_eqs:
            return self.sym(e)

        # TODO: Handle Pairing eq and Equalizer pairing eq in Cart and Lex contexts.

        # Forks
        # First find the handle, then try proving from shortest to longest
        # handle.
        if _fork and isinstance(ssource, Composition) and isinstance(starget, Composition):
            hlen = -1
            for hlen, (f, g) in enumerate(zip(
                reversed(ssource.factors),
                reversed(starget.factors),
            )):
                if not f.same(g):
                    break
            else:
                hlen += 1

            while hlen > 0:
                s = ssource.drop_head(hlen)
                t = starget.drop_head(hlen)
                e = self.prove(s, t, _fork = False)
                if e:
                    # The following line is equivalent to
                    # ```
                    # fork = e.compose_eq(ssource.source.vcomposition(
                    #     *ssource.factors[-hlen:],
                    # ).ref())
                    # ```
                    # but type-checked.
                    fork = self.c(e, *ssource.factors[-hlen:])
                    # Memoize it
                    self.proven_eqs.add((fork.ssource, fork.starget))
                    return fork

                hlen -= 1

        raise UnprovenEq(f"No equality for {ssource} and {starget}")

    # def prove(self, ssignature: tuple[MorLike, MorLike]) -> Eq | None:
    #     """Produce a proven equality from a setoid signature"""
    #     # This is used in `eq` when no `cell` is provided, in ssignature based
    #     # trans (trans with morphisms), in conversions for filling gaps.
    #     # TODO: Get rid of morphism conversions.
    #     ssource, starget = _mor_like_to_mor_ssignature(ssignature)
    #     return self._prove(ssource, starget)

    def eq(
        self, cell: EqLike | EqStub | None,
        ssignature: tuple[MorLike, MorLike] | None = None,
    ):
        """Sets name on equality and checks signature"""
        # `name` may be empty since the equality can still be accessed through
        # its signature. Some equalities don't have names and can't be
        # reproduced through operations (e.g. subobject requirements). Such
        # equalities must be registered (by method `obj`) so that they can be
        # accessed. Other equalities (e.g. hat equalities) are registered even
        # if they can be accessed by name. `cell` can also be optional when
        # there is an `ssignature`. Provided an unproven `cell` is the same as
        # providing no `cell` at all. More generally, high-level handling of
        # equalities must handle unproven equalities (by trying to prove them).
        # Currently the only operation producing an unproven equality is the hat
        # equality accessed through the morphism. Accessing subobject forks
        # through the subobject always gives proven equalities.

        # There is no point in providing a `signature` besides the `ssignature`.
        # Is `ssource` and `starget` have to be made to fit, then `cell` must
        # also be modified. However, `cell.ssource` and `cell.starget` are
        # already aligned, and making `ssource` and `starget` be aligned would
        # be the main purpose of `signature`. One would be more interested in
        # making `ssource` match `cell.ssource` and `starget` match
        # `cell.starget`. Inferring composition (besides transitivity) for
        # accomplishing this is overkill.
        if isinstance(cell, Obj):
            cell = cell.identity()

        if isinstance(cell, Mor):
            cell = cell.ref()

        if not ssignature:
            if not cell:
                raise TypeError(
                    "`ssignature is required when no `cell` is provided.",
                )

            if isinstance(cell, Axiom) or isinstance(cell, Callable):
                raise TypeError(
                    "If `cell` is callable, setoid signature is needed.",
                )

            if cell.proven:
                self.proven_eqs.add((cell.ssource, cell.starget))
            else:
                cell = self.prove(cell.ssource, cell.starget)

            return cell

        ssource, starget = _mor_like_to_mor_ssignature(ssignature)

        if not cell:
            cell = self.prove(ssource, starget)
            return cell

        if isinstance(cell, Callable):
            # There is no assumption about source being preserved here.
            cell = cell(ssource.source).ref()
        elif isinstance(cell, Axiom):
            cell = PrimEq(ssource, starget, cell)

        #cell = _fit_eq(ssource, starget, cell, self.prove)
        cell = self.t(starget, cell, ssource)

        if cell.proven:
            self.proven_eqs.add((ssource, starget))
        else:
            cell = self.prove(ssource, starget)

        return cell

    def comp_op_mor(
        self, first: MorLike, factors: Sequence[MorLike],
        straighten: Callable[[Iterator[Mor]], Iterator[Mor]] | None = None,
    ) -> Mor | Transformation:
        def noop(x: Iterator[Mor]):
            return x

        if straighten is None:
            straighten = noop

        return _compose(self.compose, first, factors, straighten)

    def comp_op_eq(
        self, first: EqLike, factors: Sequence[EqLike],
        straighten: Callable[[Iterator[Eq]], Iterator[Eq]] | None = None,
    ) -> Eq:
        def noop(x: Iterator[Eq]):
            return x

        if straighten is None:
            straighten = noop

        return _compose_eq(self.compose_eq, first, factors, straighten)

    @overload
    def c(self, first: MorLike, *factors: Mor | Obj) -> Mor: ...
    @overload
    def c(self, first: MorLike, *factors: MorLike) -> Mor | Transformation: ...
    @overload
    def c(self, first: Eq, *factors: EqLike) -> Eq: ...
    @overload
    def c(self, first: MorLike, *factors: Eq) -> Eq: ...

    def c(self, first: EqLike, *factors: EqLike,) -> Mor | Transformation | Eq:
        """Variadic high-level composition"""
        return operate_mor_or_eq(self.comp_op_mor, self.comp_op_eq, first, factors)

    def t(self, first: EqLike, *factors: EqLike):
        """Variadic high-level transitivity"""
        return _trans(self.trans, first, factors, self.prove)

ComposableT = TypeVar('ComposableT')
Composer = Callable[[tuple[ComposableT, ComposableT]], ComposableT]

def reduce[T](comp: Composer[T], factors: Iterator[T]) -> T:
    """Variadic composition"""
    acc: T | None = None
    for f in factors:
        acc = f
        break
    else:
        assert False

    for f in factors:
        acc = comp((f, acc))

    return acc

def _gen_fit_mors(source: Obj, factors: Iterator[MorLike]):
    # Polish order
    # Adapt the sources of morphisms
    for f in factors:
        f, g = _source_fit_mor_like(source, f)
        source = f.target
        yield g
        yield f

def _gen_fit_eqs(source: Obj, factors: Iterator[EqLike]):
    # Polish order
    # Adapt the sources of equalities
    for f in factors:
        if isinstance(f, Eq):
            f, g = _source_fit_eq(source, f)
            source = f.ssource.target
            yield g
            yield f
        else:
            f, g = _source_fit_mor_like(source, f)
            source = f.target
            yield g.ref()
            yield f.ref()

def _cell_source(cell: cells.Cell):
    if isinstance(cell, Obj):
        return cell

    if isinstance(cell, Mor):
        return cell.source

    return cell.ssource.source

def _obj_or_mor_to_mor(cell: Obj | Mor):
    if isinstance(cell, Obj):
        cell = cell.identity()

    return cell

def mor_like_to_mor(source: Obj, cell: MorLike):
    if isinstance(cell, Callable):
        cell = cell(source)

    return _obj_or_mor_to_mor(cell)

def _cell_to_eq(cell: cells.Cell):
    if isinstance(cell, Obj):
        cell = cell.identity()

    if isinstance(cell, Mor):
        cell = cell.ref()

    return cell

def eq_like_to_eq(source: Obj, cell: EqLike):
    if isinstance(cell, Callable):
        cell = cell(source)

    return _cell_to_eq(cell)

def _gen_fit_eqs_for_trans(factors: Iterator[Eq], prove: Prover):
    # Conversion is done adapting target from right to left.
    for f in factors:
        ssource = f.starget
        yield f
        break
    else:
        assert False

    for f in factors:
        f = _ssource_fit_eq(ssource, f, prove)
        ssource = f.starget
        yield f

def _mor_compose(comp: Composer[Mor], factors: Iterator[Mor]):
    args = list(factors)

    # Discard LazyComposition, its only purpose is type checking.
    res = reduce(comp, iter(args))
    if res.depth > 5:
        return res.source.vcomposition(*reversed(args))

    return res.expanded()

def _all_eq_or_law(
    factors: Sequence[EqLike],
) -> TypeGuard[Sequence[Eq]]:
    return all(isinstance(f, Eq) for f in factors)

def _all_mor_like(
    factors: Sequence[EqLike],
) -> TypeGuard[Sequence[MorLike]]:
    return all(isinstance(f, Obj | Mor | Callable) for f in factors)

def _all_cell(factors: Sequence[EqLike]) -> TypeGuard[Sequence[cells.Cell]]:
    return all(isinstance(f, cells.Cell) for f in factors)

def _all_obj_or_mor(factors: Sequence[MorLike]) -> TypeGuard[Sequence[Obj | Mor]]:
    return all(isinstance(f, Obj | Mor) for f in factors)

def _compose(
    comp: Composer[Mor],
    first: MorLike,
    factors: Sequence[MorLike],
    straighten: Callable[[Iterator[Mor]], Iterator[Mor]],
) -> Mor | Transformation:
    factor_it = chain(reversed(factors), (first,))
    if factors:
        last = factors[-1]
    else:
        raise ValueError("Must provide at least two factors")

    if isinstance(last, Callable):
        def _comp(source: Obj):
            # This allows having more than one transformation in factors.
            return _mor_compose(
                comp, straighten(_gen_fit_mors(source, factor_it)),
            )

        return _comp

    if isinstance(last, Obj):
        source = last
    else:
        source = last.source

    return _mor_compose(comp, straighten(_gen_fit_mors(source, factor_it)))

def _compose_eq(
    comp: Composer[Eq],
    first: EqLike,
    factors: Sequence[EqLike],
    straighten: Callable[[Iterator[Eq]], Iterator[Eq]],
) -> Eq:
    if factors:
        last = factors[-1]
    else:
        raise ValueError("Must provide at least two factors")

    if isinstance(last, Callable):
        raise ValueError("Last factor can't be transformation.")

    if isinstance(last, Obj):
        source = last
    elif isinstance(last, Mor):
        source = last.source
    else:
        source = last.ssource.source

    factor_it = chain(reversed(factors), (first,))
    return reduce(comp, straighten(_gen_fit_eqs(source, factor_it)))

def operate_mor_or_eq(
    op_mor: Callable[[MorLike, Sequence[MorLike]], Mor | Transformation],
    op_eq: Callable[[EqLike, Sequence[EqLike]], Eq],
    first: EqLike, factors: Sequence[EqLike],
):
    """Handle variadic operation for morphisms and equalities"""
    if isinstance(first, Eq):
        return op_eq(first, factors)

    if _all_eq_or_law(factors):
        return op_eq(first, factors)

    assert _all_mor_like(factors)
    return op_mor(first, factors)

# TODO: How does one handle defensive args? It seems `compose` would have to
# be wrapped inside a function that accepts type object instead of MorLike, etc.
# and then does dynamic type-checking. This dynamic type-checking would obviously
# be part of the internalization (using a theory as backend).
# This would require a separate `composer`, which seems to kill the point of having
# typed comp and comp_eq args!
# The way to go is too keep all the type annotations and wrap dynamically type-checked
# functions. For defensive type checking one also relies on wrapping the non-annotated
# functions and initialized the Defensive argument in the wrapper. It may be the case
# however that a non-annotated callable can be used as Composer[T].
# Should one directly instantiate Composition instead of leaving as LazyComposition?
# Variadic compose being outside the theory doesn't have a way to handle type checking
# beyond the binary compose functions that underlie it.

def _same_source(first: cells.Cell, factors: Sequence[cells.Cell]):
    source = _cell_source(first)
    return all(_cell_source(f).identical(source) for f in factors)

def operate_mor_common_source(
    op: Callable[[Iterator[Mor]], Mor],
    first: MorLike, factors: Sequence[MorLike],
    rev: bool = False,
):
    """Handle operation on morphisms where common source is expected"""
    if (
        isinstance(first, Obj | Mor) and _all_obj_or_mor(factors)
        and _same_source(first, factors)
    ):
        factor_it = (
            _obj_or_mor_to_mor(x)
            for x in _sequence_to_iterator(first, factors, rev)
        )
        return op(factor_it)

    def _t(source: Obj):
        factor_it = (
            mor_like_to_mor(source, x)
            for x in _sequence_to_iterator(first, factors, rev)
        )
        return op(factor_it)

    return _t

def operate_eq_common_source(
    op: Callable[[Iterator[Eq]], Eq],
    first: EqLike, factors: Sequence[EqLike],
    rev: bool = False,
):
    """Handle operation on equalities where common source is expected"""
    if (
        isinstance(first, cells.Cell) and _all_cell(factors)
        and _same_source(first, factors)
    ):
        factor_it = (
            _cell_to_eq(x)
            for x in _sequence_to_iterator(first, factors, rev)
        )
        return op(factor_it)

    raise ValueError("Requires cells with the same source")

def _sequence_to_iterator[T](
    first: T, factors: Sequence[T], rev: bool,
) -> Iterator[T]:
    if rev:
        return chain(reversed(factors), (first,))

    return chain((first,), factors)

def _trans(
    trans_: Composer[Eq], first: EqLike,
    factors: Sequence[EqLike], prove: Prover,
) -> Eq:
    def op(it: Iterator[Eq]):
        return reduce(trans_, _gen_fit_eqs_for_trans(it, prove))

    return operate_eq_common_source(op, first, factors, rev=True)
