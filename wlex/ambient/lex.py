"""High level interface fo the lex ambient"""
from itertools import chain
from typing import override

from .cells import Obj, Mor, Eq
from . import cart
from .cells.cart import Product
from .cells.lex import Subobject, EqualizerMor
from .public import lex as public

# TODO: When implementing extensive context recall the relation between
#       restriction and overloading.

class LexContext(cart.CartContext):
    """Handles cells of a theory with ambient lex"""
    __slots__ = ()

    equalizer = staticmethod(public.equalizer)
    equalizer_pairing = staticmethod(public.equalizer_pairing)
    equalizer_pairing_unique = staticmethod(public.equalizer_pairing_unique)

    def restrict(self, mor: Mor, target: Obj):
        # This has to be used after conversion has been inferred, so that
        # `target` is a (strict) subobject of `mor.target`.

        # TODO: Type checking here or make this private.
        #       The condition is target.sup.identical(mor.target.sup)
        #       What happens if some of the requirements are already
        #       fulfilled by mor.target??
        #       What should happen is that the lifting has no effect for
        #       such requirements, or rather that the subobject skips such
        #       requirements, because in their version precomposed with `mor`
        #       they are already implied by the existing requirements?
        # TODO: Handle case where target is too large? (only mediating inclusion is needed)
        # TODO: Some EqualizerMor are extensionally equal to their supermorphism.
        #       Some inclusions are extensionally identities.

        if mor.target.identical(target):
            return mor

        # Restricting means precomposing with an inclusion to allow lifting to a
        # subobject.
        requirements = target.requirements - mor.target.requirements
        if not requirements:
            # TODO: Handle with conversion!
            return mor.target.incl(target).compose(mor)

        source = Subobject(mor.source, (
            (ssource.compose(mor), starget.compose(mor))
            for ssource, starget in requirements
        ))

        return EqualizerMor(mor.compose(source.incl(mor.source)), target)

    @override
    def prod(self, first: tuple[str | int, Obj], *params: tuple[str | int, Obj]):
        # Extract requirements of all subobject components and use them to turn
        # the product into a subobject of the product.
        sup = super().prod(
            *((l, p.sup) for l, p in chain((first,), params))
        )

        if all(p is p.sup for _, p in chain((first,), params)):
            return sup

        assert isinstance(sup, Product)
        # TODO: compose_eq needs the restriction!
        #       The source of the requirement is an intermediate subobject!
        reqs = chain(*(
            ((l, req.compose_eq()))
        ))

        # No need to type check the sources of the parallel pairs?
        # TODO: Use `requiring` instead of directly using Subobject.

        # TODO: More type checking?