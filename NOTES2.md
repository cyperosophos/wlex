TODO: Coprojections should support conversions just like projections.
TODO: weakening flag must be in the ambient?

TODO: Consider implementing W-Cart. W-Types don't require all limits.
In this case one would have two possible backends for Category:
one based on ambient Lex, and another based on ambient Dist (extensive cartesian).
In the latter `compose` relies on the Maybe monad.
See: nlab/ Polynomial functor (literal polynomial functor)
See: nlab/ Polynomail monad (free monoid)
See: nlab/ Extensive category
See: nlab/ Distributive categories

    def includes(self, prod: Obj) -> bool:
        """All the components of `prod` are components of `self`."""
        # Notice that, if all the names in `prod` are `int`, then `prod` will
        # count is included solely based on the component types.
        if isinstance(prod, Product):
            return all(
                name in self.components
                and self.name_to_obj(name) == prod.name_to_obj(name)
                for name in prod.names
            )
        return ...

Unsourced projection can take a non Product as source, making it become an identity.

One can have the high-level pairing
itself accept keys as arguments instead of only morphisms.
Having compose also accept keys is probably overkill and
too complicated since one would then have to distinguish
coprojections and param projections.

Param projections are
the way one handles vars within the body of a morphism (check
prev notes). The idea should be simple. There are access ops
(i.e. projections) and assignments. Assignments expand the
product element, and access ops are the usual projections.
Assignments are pairings with the identity.
Nothing changes about the composition. It seems there is a benefit to
supporting parallel assignments. Whereas naturality doesn't translate
to parallelism but simply to the choice two equal compositions,
parallel assignment can be interpreted as such in the appropriate
computational environment. This isn't simply a matter of optimization,
but of explicitly representing the program.
Parallel assignment are invisible to each other. This is useful.

There should also be UnsourcedProductMor which can only be the result
of having a pairing (ProductMor) consisting only of unsourced morphisms.
When not all morpshisms are unsourced, one must use these to determine
the source of the unsourced morphisms.