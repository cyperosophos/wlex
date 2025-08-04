th is the Theory. It can be the generated theory or the
meta theory. Here the required theory is just the theory
of categories. For Category one needs Lex, etc.
theory includes kw and prefix.
the meta theory may skip some type checking (lex type checking)?
theory is just an interface mimicking the syntax as much as possible,
but following the principle of "only one way" more strictly,
therefore it does not reflect syntax sugar.
All proofs must be provided.
Use the hierarchy Cat > Cart > Lex (lex with products then equalizers)

TODO: What about assigning value to a Mor for which
the signature has been provided?
Provide signature and definition in the same line.

dummy ambients are used for skipping type checking.

What about inductive type quiver?
Allow it implicitly. Recursive function is defined as copair.
This is especially required for monads.

```py
class N(wlex.Quiver):
    Zero = _()
    Succ = _('N')

def Monad(C):
    class D(wlex.Quiver): # or wlex.WLex?
        T = _(C)
        unit = _(_ >> T)
        mul = _(T.T >> T)
        left_unit = _(mul @ unit.T == T)
        right_unit = _(mul @ T.unit == T)
        assoc = _(mul @ mul.T == mul @ T.mul)
    return D

class C(wlex.Quiver):
    M = own(Monad('C')) # so that M.T.T or _.T.T can be written  instead of M.T.M.T
```
