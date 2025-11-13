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

(f @ a$, g @ b$) @ (a=m, b=n)
becomes (f @ m, g @ n)
(f @ a$, g @ b$) @ p
can't become (f @ a$p, g @ b$p)
The idea is then that if a morphism gets repeated during simplification
then simplification doesn't go through.
Duplication of projections (and identities) is allowed! (but not composition of projections?)
(f @ a$, g @ b$) @ (a=m @ x$, b=n @ y$) @ (x=s $u, y=t $v)
becomes (f @ m @ s, g @ b @ t)
$u comes from local namespace. It acts like a constant in the composition
although it is a projection.
(a$, b$) @ (a=x$, b=y$, c=y$) @ (x=s $u, y=t $v)
right
(a$, b$) @ (a=s $u, b=y$, c=y$) @ (y=t $v)
(s $u, y$) @ (y=t $v)
more accurately (it makes more sense to interpret it thus when parsing syntax,
so that the id here would have to be explicitly included.)
(s $u, y$) @ (id, y=t $v) # maybe this is not needed.
(s $u, t $v)
left
(x$, y$) @ (x=s $u, y=t $v)
(s $u, t $v)

(a$, b$, b$) @ (a=x$, b=y$) @ (x=s $u, y=t $v)
(x$, y$, y$) @ (x=s $u, y=t $v)

(x=(m=a$, n=b$), y=c$) @ (a=1, b=2, c=3)

Composed projection becoming single projection
a$ x$ (x=(a=$m))
$m
(s=u$, t=u$) @ (u=a$ x$) @ (x=(a=$m))
Not treating composition of projections as projection leads to needing backtracking.
What about pairing of projections? This should also count as projection, just like composition of projections.

(m$, n$) @ (u=x$, v=x$) @ (x=(m=a$, n=b$))
(m$ x$, n$ x$) @ (x=(m=a$, n=b$))
(a$, b$)

(u=x$, v=x$) @ (x=(m=a$, n=b$)) @ (a=r$, b=s$, c=t$)
(u=(m=a$, n=b$), v=(m=a$, n=b$)) @ (a=r$, b=s$, c=t$)
(u=(m=r$, n=s$), v=(m=r$, n=s$))
Pairing of projections length looks like a semiinvariant?

(m$, n$) @ (u=x$, v=x$) @ (x=(m=a$, n=b$)) @ (a=r$, b=s$, c=t$)
(a$, b$) @ (a=r$, b=s$, c=t$)
(r$, s$)

Backtracking with projection composition
a$ x$ (x=(a=$m))

(a$, b$) @ (x$, y$) @ (x=(a=$m), y=(b=$n))
(a$, b$) @ (a=$m, b=$n)
($m, $n)

Recall that x$ has source and target.
(a$ (x$, y$), c$ (x$, y$)) @ (x=(a=$m, b=$n), y=(c=$p), z=(d=$q))
(a$ x$, c$ y$) @ ...
($m, $p)

To avoid backtracking combine projections into single morphism.
"Shrink" projections if needed when composing with a component.
Order of execution may change, and this is ok. Composing with an intensional identity avoids this.

fn f: X -> Y
f = g h
One possibility is that this makes f defined and introduces an eq.
f and g h would then be only intensionally equal. The other possibility is to make f the same as g h.

eq e: f -> g
e = c d
If e is made to be c d, then it is automatically defined.

def _is_proj(mor: Mor):
    # Projection or made out of projections. As stated above terminal morphisms
    # get excluded from components.
    return isinstance(mor, Projection) or (
        isinstance(mor, ProductMor) and all(
            _is_proj(m) for _, m in mor.components
        )
    )

Variadic functions with conversions, etc. of course cannot be the result of compiling
the ambient theory, as this would be too complicated (although accomplishable with List, etc.),
so they are built on simple functions which take care of type checking the arguments.
What about the rest of the body of such complicated functions? Just assume the return type is correct.
No point in doing defensive type checking. The instantiation functions (obj, mor, eq) are also not part of the theory.