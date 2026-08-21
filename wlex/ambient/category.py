"""High level interface to category ambient"""
from collections.abc import Callable, Iterator, Sequence
from abc import ABCMeta, abstractmethod
from typing import Any, Self, TypeGuard, TypeVar, overload #, NoReturn
from itertools import chain
import dataclasses

from .cells import Obj, Mor, Eq, MorStub, EqStub, PrimEv, Axiom, Name
from .cells.category import Composition
from . import cells
from .public import category as public

Transformation = Callable[[Obj], Mor]
MorLike = Mor | Obj | Transformation
EqLike = MorLike | Eq
Prover = Callable[[Mor, Mor], Eq]

class UnprovenEq(Exception):
    pass

def check_signature(source: Obj, target: Obj, cell: Mor):
    if not source.identical(cell.source):
        raise cells.SourceUnfit("Wrong source", source, cell.source)

    if not target.identical(cell.target):
        raise cells.TargetUnfit("Wrong target", cell.target, target)

def _trim_or_proj(source: Obj, target: Obj):
    proj = source.obj_to_proj(target)
    no_proj = proj.target.identical(source.terminal())
    try:
        trim = source.trim(target)
    except ValueError:
        if no_proj:
            raise

        return proj

    if no_proj:
        return trim

    raise ValueError("Ambiguous choice of trim or projection")

def _source_trim_mor_like(source: Obj, cell: MorLike):
    if isinstance(cell, Callable):
        cell = cell(source)

    if isinstance(cell, Obj):
        cell = cell.identity()

    try:
        sconv = _trim_or_proj(source, cell.source)
    except ValueError as exc:
        raise cells.SourceUnfit(
            "Can't trim source", source, cell.source,
        ) from exc

    #return cell.compose(sconv)
    return cell, sconv

def _source_trim_eq(source: Obj, cell: Eq):
    try:
        sconv = _trim_or_proj(source, cell.ssource.source)
    except ValueError as exc:
        raise cells.SourceUnfit(
            "Can't trim source", source, cell.ssource.source,
        ) from exc

    #return cell.compose_eq(sconv.ref())
    return cell, sconv.ref()

def _ssource_trans_eq(ssource: Mor, cell: Eq, prove: Prover):
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

    return cell, sconv

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

# TODO: Use special field in Stub to make sure each field is only
# accessed once? This still allows cheating. It's better to handle
# this at the level of PrimEv and Axiom. Even better: make a Stub
# wrapper around these that also handles Obj, so that even if the
# underlying value is a true cell (as when providing cells of a subtheory)
# it can only be used once. This wrapper should also handle the None
# value (when no value has been provided) and overriding cells when
# defining subtheory.

class Once[T]:
    __slots__ = '_value', '_used'
    _value: T | None
    _used: bool

    def __init__(self, value: T | None = None):
        self._value = value
        self._used = False

    @property
    def value(self):
        if self._used:
            raise ValueError("Can only be used once")

        v = self._value
        if v is None:
            raise ValueError("No value was provided.")

        self._used = True
        return v

    @value.setter
    def value(self, v: T | None):
        #if v is None:
        #    return

        # TODO: Is this needed?
        #if not isinstance(v, (Obj, Mor, Eq, Theory)):
        #    raise ValueError("Expected cell or theory")

        self._value = v

    @staticmethod
    def prim[V](stub: 'OnceUpdate[V]') -> V:
        if isinstance(stub, OnceStub):
            return stub.use()

        stub, update = stub
        return stub.use(update)

def of_type[T](x: object, typ: type[T]) -> T:
    assert isinstance(x, typ)
    return x

class OnceStub[T]:
    __slots__ = 'stub', '_used'
    stub: T
    _used: bool

    def __init__(self, stub: T):
        # The underlying stub can be accessed many times when updating its
        # attibutes, but only once (by calling `use`) when using it as the
        # argument from creating the theory.
        self.stub = stub
        self._used = False

    def use(self, update: Callable[[T], None] | None = None) -> T:
        if self._used:
            raise ValueError("Can only be used once")

        stub = self.stub

        if isinstance(stub, Theory):
            raise TypeError("Expected stub")

        if update:
            update(stub)

        self._used = True
        return stub

S = TypeVar('S')
OnceUpdate = tuple[OnceStub[S], Callable[[S], None]] | OnceStub[S]

# class Theory2(metaclass=ABCMeta):
#     """Base class for theories"""

#     Stub: type[TheoryStub]

#     @abstractmethod
#     @classmethod
#     def from_prim(cls, ctx: Any, prim: Any) -> Self:
#         """Create theory from primitives"""
#         # Some rules must be followed in the implementation, which are not
#         # enforced through code. Attributes of `prim` must be used exactly once
#         # to define variables of the same name. These variables must then be
#         # used instead of accessing the attributes.
#         # TODO: primitives can't be changed through conversion
#         #       (including Obj -> Mor through identity, etc.)!
#         # TODO: primitives shouldn't be used (e.g. in composition, identity, etc.)
#         #       before being named.

#     @classmethod
#     def is_own_stub(cls, stub: TheoryStub):
#         """Stub corresponds to theory"""
#         return isinstance(stub, cls.Stub)

@dataclasses.dataclass(frozen=True)
class Theory(metaclass=ABCMeta):
    name: Name = dataclasses.field(default_factory=Name, kw_only=True)

    @classmethod
    @abstractmethod
    def from_ctx(cls, ctx: 'Context[Any]') -> Self:
        """Creates theory from context"""

    def __post_init__(self):
        if not dataclasses.is_dataclass(self):
            raise TypeError("Subclass must be dataclass")

        for field in dataclasses.fields(self):
            v = getattr(self, field.name)
            if isinstance(v, (Obj, Mor, Theory)):
                v.name.parent = self.name

# TODO: When implementing theories, type is already handled by context,
# and pylance type-checking is too limited and makes implementation cumbersome.
# The difficulty of tracking types arrises with subtheories.

class Hat[V: Theory]:
    def __init__(
        self, ctx: 'Context[V]',
        hat_source: Mor, hat_target: Mor,
        cell: Mor,
    ):
        self.ctx = ctx
        self.hat_source = hat_source
        self.hat_target = hat_target
        self.cell = cell

    def __call__(self, c: EqLike | Once[EqStub] | None):
        # We defer assigning hat, because we may end up needing cell in its
        # definition.
        return self.ctx.eq(
            c, (self.hat_source, self.hat_target.compose(self.cell)),
        )

    def invert(self):
        return type(self)(
            self.ctx,
            self.hat_source, self.cell,
            self.hat_target,
        )

class Context[V: Theory]:
    """Handles cells of a theory with ambient category"""
    __slots__ = 'proven_eqs', 'obj_refs', 'mor_refs', 'sub_refs', 'theory_cls'
    #name_stack: tuple[str, ...]
    proven_eqs: set[tuple[Mor, Mor]] # set of ssignatures
    obj_refs: dict[str, Obj]
    mor_refs: dict[str, Mor]
    sub_refs: dict[str, Theory]
    theory_cls: type[V]

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

    @staticmethod
    def copy_name[W: Obj | Mor](src: W, cell: W) -> W:
        cell.name = src.name
        return cell

    @staticmethod
    def copy_name_to_target(src: Obj, cell: Mor) -> Mor:
        cell.target.name = src.name
        return cell

    def __init__(self, theory_cls: type[V]): # TODO: forbid subclasses of V?
        #proven_eqs: set[tuple[Mor, Mor]] | None = None):
        #self.name_stack = ()

        # if proven_eqs is None:
        #     self.proven_eqs = set()
        # else:
        #     self.proven_eqs = proven_eqs

        self.proven_eqs = set()
        self.obj_refs = {}
        self.mor_refs = {}
        self.sub_refs = {}
        self.theory_cls = theory_cls

    id = identity

    def sub[T: Theory](
        self, name: str,
        prog: 'Context[T]',
    ) -> T:
        # Notice that `sub` and `obj` deal only with primitives (stubs).
        # `prog` is a completed context.
        theory = prog.theory_cls.from_ctx(prog)
        self.proven_eqs.update(prog.proven_eqs)
        return self.define(name, theory)

    def define[T: Obj | Mor | Theory](self, name: str, cell: T) -> T:
        # Create reference and rename.
        cell.name.base = name
        if isinstance(cell, Obj):
            self.obj_refs[name] = cell
        elif isinstance(cell, Mor):
            self.mor_refs[name] = cell
        else:
            self.sub_refs[name] = cell

        return cell

    def obj(self, name: str, stub: Once[Obj]):
        """Sets name on object"""
        cell = stub.value
        self.define(name, cell)
        return cell

    @overload
    def iso(
        self, name: str, cell_or_stub: MorLike | Once[MorStub],
        signature: tuple[Obj, Mor | Transformation],
    ) -> tuple[Mor, Hat[V], Hat[V]]: ...
    @overload
    def iso(
        self, name: str, cell_or_stub: MorLike | Once[MorStub],
        signature: tuple[Obj, Obj, Mor | Transformation],
    ) -> tuple[Mor, Hat[V], Hat[V]]: ...

    def iso(
        self, name: str, cell_or_stub: MorLike | Once[MorStub],
        signature: tuple[Obj, Mor | Transformation] | tuple[Obj, Obj, Mor | Transformation],
    ) -> tuple[Mor, Hat[V], Hat[V]]:
        """Defines isomorphism by requiring an extra equality"""
        if len(signature) == 3:
            s, t, r = signature
            mor_signature = s, t, s, r
        else:
            mor_signature = signature

        res, hat = self.mor(name, cell_or_stub, mor_signature)

        # An extra hat is required, which reverses the composition in the first hat.
        ihat = hat.invert()
        return res, hat, ihat

    @overload
    def mor(
        self, name: str, cell_or_stub: MorLike | Once[MorStub],
        signature: tuple[Obj, Obj],
    ) -> Mor: ...
    @overload
    def mor(
        self, name: str, cell_or_stub: MorLike | Once[MorStub],
        signature: tuple[Obj, Mor | Transformation],
    ) -> tuple[Mor, Hat[V]]: ...
    @overload
    def mor(
        self, name: str, cell_or_stub: MorLike | Once[MorStub],
        signature: tuple[Mor | Transformation, Mor | Transformation],
    ) -> tuple[Mor, Hat[V]]: ...
    @overload
    def mor(
        self, name: str, cell_or_stub: MorLike | Once[MorStub],
        signature: tuple[Obj, Obj, Obj, Mor | Transformation],
    ) -> tuple[Mor, Hat[V]]: ...
    @overload
    def mor(
        self, name: str, cell_or_stub: MorLike | Once[MorStub],
        signature: tuple[Obj, Obj, Mor | Transformation, Mor | Transformation],
    ) -> tuple[Mor, Hat[V]]: ...
    @overload
    def mor(
        self, name: str, cell_or_stub: Obj | Mor,
        signature: None = None,
    ) -> Mor: ...

    def mor(
        self, name: str, cell_or_stub: MorLike | Once[MorStub],
        signature: tuple[MorLike, MorLike] | tuple[Obj, Obj, MorLike, MorLike] | None = None,
    ):
        """Sets name on morphism and checks signature"""
        if isinstance(cell_or_stub, Once):
            cell = cell_or_stub.value
            assert isinstance(cell, MorStub)
        else:
            cell = cell_or_stub

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

            self.define(name, cell)
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
                self.define(name, cell)
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

            return self._hat_mor(
                name, cell,
                (source, target.source),
                (final_source, final_target),
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

        return self._hat_mor(
            name, cell,
            (source.source, target.source),
            (final_source, final_target),
            (source, target),
        )

    def _hat_mor(
        self, name: str, cell: Mor,
        signature: tuple[Obj, Obj],
        final_signature: tuple[Obj | None, Obj | None],
        hat_signature: tuple[Mor, Mor],
    ) -> tuple[Mor, Hat[V]]:
        """Sets name on morphism and checks signature"""
        final_source, final_target = final_signature
        source, target = signature
        #cell = _fit_mor(source, target, cell)
        cell = self.c(target, cell, source)

        if final_source:
            assert final_target
            check_signature(final_source, final_target, cell)
        else:
            check_signature(source, target, cell)

        hat_source, hat_target = hat_signature

        _hat = Hat(self, hat_source, hat_target, cell)
        self.define(name, cell)
        return cell, _hat

    def prove(self, ssource: Mor, starget: Mor, _fork: bool = True) -> Eq:
        # Reflexivity
        if ssource.same(starget):
            return self.ref(ssource)

        e = ssource.source.postulate(ssource, starget)
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
                    # Memoize it by adding directly to `proven_eqs`, since the
                    # point of doing so is that we expect to perhaps use the
                    # exact same equality again.
                    self.proven_eqs.add((fork.ssource, fork.starget))
                    return fork

                hlen -= 1

        raise UnprovenEq(f"No equality for {ssource} and {starget}")

    def sharpen(self, x: Obj, y: Obj):
        # Compose with the result using `self.c`.
        if x.identical(y):
            return x

        raise ValueError("Can't sharpen")

    def _sharp_prove(self, f: Mor, g: Mor):
        edge = self.sharpen(f.target, g.target)
        return self.prove(self.c(edge, f), self.c(edge, g))

    def eq(
        self, cell_or_stub: EqLike | Once[EqStub] | None,
        ssignature: tuple[MorLike, MorLike] | None = None,
    ):
        """Sets name on equality and checks signature"""
        if isinstance(cell_or_stub, Once):
            cell = cell_or_stub.value
            assert isinstance(cell, EqStub)
        else:
            cell = cell_or_stub

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
                    "`ssignature` is required when no `cell` is provided.",
                )

            if isinstance(cell, Axiom) or isinstance(cell, Callable):
                raise TypeError(
                    "If `cell` is callable, setoid signature is needed.",
                )

            # Globular conditions are already fulfilled here.
            if cell.proven:
                self.register_equality(cell.ssource, cell.starget)
            else:
                cell = self.prove(cell.ssource, cell.starget)

            return cell

        ssource, starget = _mor_like_to_mor_ssignature(ssignature)

        if not cell:
            return self._sharp_prove(ssource, starget)

        if isinstance(cell, Callable):
            # There is no assumption about source being preserved here.
            cell = cell(ssource.source).ref()
        elif isinstance(cell, Axiom):
            cell = cell.to_eq(ssource, starget)

        #cell = _fit_eq(ssource, starget, cell, self.prove)
        # TODO: incl_join in trans, sharpen? In this case sharpen must be
        # all equalities (eqlikes) before _ssource_trans_eq, etc.
        cell = self.t(starget, cell, ssource)

        if cell.proven:
            self.register_equality(ssource, starget)
        else:
            cell = self._sharp_prove(ssource, starget)

        return cell

    def register_equality(self, ssource: Mor, starget: Mor):
        # One overrides this so that e.g. pairing equalities get split,
        # i.e. composed with all possible projections.
        self.proven_eqs.add((ssource, starget))

    def straighten_mors(self, factors: Iterator[Mor]):
        return factors

    def straighten_eqs(self, factors: Iterator[Eq]):
        return factors

    def comp_op_mor(
        self, first: MorLike, factors: Sequence[MorLike],
    ) -> Mor | Transformation:
        return _compose(self.compose, first, factors, self.straighten_mors)

    def comp_op_eq(
        self, first: EqLike, factors: Sequence[EqLike],
    ) -> Eq:
        return _compose_eq(self.compose_eq, first, factors, self.straighten_eqs)

    @overload
    def c(self, first: MorLike, *factors: Mor | Obj) -> Mor: ...
    @overload
    def c(self, first: MorLike, *factors: MorLike) -> Mor | Transformation: ...
    @overload
    def c(self, first: Eq, *factors: EqLike) -> Eq: ...
    @overload
    def c(self, first: MorLike, *factors: Eq) -> Eq: ...

    def c(self, first: EqLike, *factors: EqLike) -> Mor | Transformation | Eq:
        """Variadic high-level composition"""
        return operate_mor_or_eq(self.comp_op_mor, self.comp_op_eq, first, factors)

    def t(self, first: EqLike, *factors: EqLike):
        """Variadic high-level transitivity"""
        def trans(x: tuple[Eq, Eq]) -> Eq:
            d, e = x
            edge = self.sharpen(d.ssource.target, e.ssource.target)
            return self.trans((
                self.c(edge, d),
                self.c(edge, e),
            ))

        return _trans(trans, first, factors, self._sharp_prove)

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
        f, g = _source_trim_mor_like(source, f)
        source = f.target
        yield g
        yield f

def _gen_fit_eqs(source: Obj, factors: Iterator[EqLike]):
    # Polish order
    # Adapt the sources of equalities
    for f in factors:
        if isinstance(f, Eq):
            f, g = _source_trim_eq(source, f)
            source = f.ssource.target
            yield g
            yield f
        else:
            f, g = _source_trim_mor_like(source, f)
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
    # Conversion is done adapting starget from right to left.
    # Polish order. Notice call to _sequence_to_iterator in
    # operate_eq_common_source and `rev` flag.
    for f in factors:
        ssource = f.starget
        yield f
        break
    else:
        assert False

    for f in factors:
        f, g = _ssource_trans_eq(ssource, f, prove)
        ssource = f.starget
        yield g # targets of f and prev equality must be adapted to target of g using Context.c
        yield f

def _mor_compose(comp: Composer[Mor], factors: Iterator[Mor]):
    args = list(factors)

    # Discard LazyComposition, its only purpose is type checking.
    res = reduce(comp, iter(args))
    if res.depth > 5:
        return res.source.vcomposition(*reversed(args))

    return res.expanded()

def _any_eq(
    factors: Sequence[EqLike],
) -> bool:
    return any(isinstance(f, Eq) for f in factors)

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

def cell_source(cell: cells.Cell):
    if isinstance(cell, Obj):
        return cell

    if isinstance(cell, Mor):
        return cell.source

    return cell.ssource.source

def cell_target(cell: cells.Cell):
    if isinstance(cell, Obj):
        return cell

    if isinstance(cell, Mor):
        return cell.target

    return cell.ssource.target

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

    source = cell_source(last)

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

    if _any_eq(factors):
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

    def _t(source: Obj):
        factor_it = (
            eq_like_to_eq(source, x)
            for x in _sequence_to_iterator(first, factors, rev)
        )
        return op(factor_it)

    for cell in chain((first,), factors):
        if isinstance(cell, cells.Cell):
            return _t(cell_source(cell))

    raise ValueError(
        "At least one factor must be a cell, not a transformation.",
    )

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
