from typing import Union, TypeVar
from collections.abc import Sequence, Mapping

from . import category

ProductParam = tuple[str, 'Obj'] | tuple[tuple[str, ...], 'Product']
ProductParamName = Union[str, 'Obj']
ProductParamKey = int | ProductParamName
ProductMorParam = tuple[str | tuple[str, ...], 'Mor']
ProductProjParam = tuple[str | tuple[str, ...], ProductParamKey]
# TODO: Include all Cart cells here, e.g. Product, ProductMor

class Obj(category.Obj):
    # TODO: Keep high-level interface in the ambient class (Cart).
    # It seems that having a proj method in Product makes sense,
    # since they proj corresponds to the legs of the span returned
    # by the theoretical product morphism,
    # however it's not clear that a multiarg proj is sufficiently
    # low level to be had here. One can have the high-level pairing
    # itself accept keys as arguments instead of only morphisms.
    # Having compose also accept keys is probably overkill and
    # too complicated since one would then have to distinguish
    # coprojections and param projections. Param projections are
    # the way one handles vars within the body of a morphism (check
    # prev notes). The idea should be simple. There are access ops
    # (i.e. projections) and assignments. Assignments expand the
    # product element, and access ops are the usual projections.
    # Assignments are pairings with the identity.
    # Nothing changes about the composition. It seems there is a benefit to
    # supporting parallel assignments. Whereas naturality doesn't translate
    # to parallelism but simply to the choice two equal compositions,
    # parallel assignment can be interpreted as such in the appropriate
    # computational environment. This isn't simply a matter of optimization,
    # but of explicitly representing the program.
    # Parallel assignment are invisible to each other. This is useful.
    def proj(
            self, *args: ProductParamKey | ProductProjParam,
            **kwargs: ProductParamKey,
        ):
        from ..cart import ProductMor
        if not (args or kwargs):
            return ProductMor(self, ())
        
        if len(args) > 0:
            if len(args) > 1 or kwargs:
                raise ValueError
            arg = args[0]
            if isinstance(arg, tuple):
                name, key = arg
            else:
                name = ''
                key = arg
        elif len(kwargs) > 1:
            raise ValueError
        else:
            # Notice that the type checker is permissive here.
            name, key = list(kwargs.items())[0]

        if key == self:
            mor = self.identity()
            if name:
                return ProductMor(self, ((name, mor),))
            return mor
        raise ValueError
    
    @staticmethod
    def terminal():
        from ..cart import Product
        return Product(())
    
    def terminal_mor(self):
        # The result of this has to pass backend.TerminalMor.check.
        #return Mor(self, Product(()))
        # TODO: Use this instead for purity
        return self.proj()
        # See cart.weaken_mor
    
    def product(self, y: 'Obj'):
        from ..cart import Product
        # This result of this has to pass backend.Span.check.
        # We use Product for purity (since it defines __eq__),
        # but we don't need its check method. When definining the
        # backend theory, the morphisms returned here are not used
        # as projections, so there is no need for eval (although
        # one still should have purity and composition).
        x = self
        source = Product((('x', x), ('y', y)))
        #return Mor(source, x), Mor(source, y)
        # Use proj for purity
        return source.proj('x'), source.proj('y')

class PrimObj(category.PrimObj, Obj):
    pass