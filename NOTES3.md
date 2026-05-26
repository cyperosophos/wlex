# Minimal explicit syntax

Compositions are mostly explicit, there are no implicit projections or coprojections.
The first is by having permutations and renamings of (co)projections (isomorphisms) inserted into compositions.
The second way in which composition is corrected (implicit) is by having morphisms lifted and restricted from left to right.
The names of coprojections are global, because coprojections can't
be treated as transformations, one can't infer their target from
their source? Allow "cotransformations" (cf. lifting to equalizer)!

There are two (co)projections, the ones based on names, and the ones based on indices. Named (co)projections are affected by flattening (and parameter repetition). Indexed coprojections are based on the initialization arguments of the (co)product. Pairing instantiates a product and is allowed to not give names. Since pairings need to have a target (product), it makes sense that products are also allowed to have unnamed parameters.
We still require argument naming to follow rules based on
python args kwargs syntax.

Coproduct syntax (select, etc.)
TODO: what does this have to do with extensivity?

f: [X, Y] -> Z
g: X -> Z
h: Y -> Z
f = [g, h]

f: Z -> [A, B]
X := (
    A, Z,
    f @ $1 = !0 @ $0,
)
Y := (
    B, Z,
    f @ $1 = !1 @ $0,
)
[X, Y] ~= [A, B]
// This should make overloading possible!
// If the top row is coproduct, then the two com squares are pullbacks.
// This means that, like in the case of equalizer lifting/restricting, one can get the right target by requiring the right source. One still cannot infer coprojections like inclusions, because of e.g. A -> A+A being ambiguous.
// See: /home/gabriel/old/eudoxos-2025/Documents/Codeberg/lab/catopy/catopy/theory/
// f @ [$1 @ X, $1 @ Y] = [!0 @ $0 @ X, !1 @ $0 @ Y]
U := (
    A, [X, Y],
    f @ [$1 @ X, $1 @ Y] @ $1 = !0 @ $0,
)
// If [$1 @ X, $1 @ Y] is iso, then U ~= X.
// If U ~= X and V ~= Y, then [$1 @ X, $1 @ Y] is iso??
// is there a simple condition that will make this true?

h: Z -> 2
X := (Z, h == 0)
Y := (Z, h == 1)
![$0 @ X, $0 @ Y]: Z -> [X, Y] // Is this useful??
// The idea is that just like one can have copairings functions
// [X, Y] -> U, one can also have functions Z -> U by defining
m: (Z, h = 0) -> U
n: (Z, h = 1) -> U
`[m, n]: Z -> U`
// Support other sets besides 2? E.g. 3, {a, b, c}, etc.
// Supporting these shows consistency with variadic syntax.
// It doesn't make sense to use functions instead of elements,
// because overlaps get more complicated.
// All conditions can be reduced to this form by having the
// right side just be a boolean.
// The meaning of [X, Y] is just an object such that X and Y
// are certain equalizers.
// [a: X, b: X] @ X is not allowed due to the ambiguity.
// The best solution seems to disallow [X, X] altogether even
// if there are labels. Allow defining isomorphic types
// (not aliases), for which the isomorphism is never applied
// implicitly.
// Coprojections are inclusions, so they are implicit.
// Projections are always explicit.
// Single component products are always labeled?
// X = (a: Y) is an isomorphic type, with explicit isomorphism
// i.e. the projection $a.
// Allow labels in coproduct to ease copairing syntax?
// Labels in this case are elements of a finite set such as {0, 1},
// they are arrows in the equalizer forks.
// If types can't be repeated, then there is no need for labels.
// Treat [X, Y] and [Y, X] as identical!
// [X, (a: X)] @ (a: X)


// W-Types
N = [zero: (), succ: N]
fibo: N -> (int, int)
fibo = [
    zero = (0, 1),
    succ = ($1, $0 + $1),
]
// With multiple types, the (non-initial) algebra occurs in an overcategory.

N = () + N
fibo: N -> (int, int)
fibo = [(0, 1), ($1, $0 + $1)]

# Syntax sugar

Imperative style composition. Does this rely on weakening morphisms?

# Interface

interface D {
    type X: C;
    fn f: X -> N;
}

// This is just based on projections from 2-limit
fn h: (D.X, N) -> N = add @ (D.f @ $0, $1);
// Write `h[A]` to use a specific implementation?
// Why would h be a nat trans? `h[g]` is equality.

// Pairing is implementation
type A: D = {
    X = P;
    f = s;
}

// Nat trans but not a priori?
// It's unclear how useful this would be.
fn h: A -> B = {
    X = m;
    f = e; // equality
}

// eq ...

# Specifications

Recall that A + B + C is the pushout of a certain pair of
coprojections. This suggests one does not need to allow all
2-pushouts.

Canonical inclusions are a convenience. Should one just support unions instead of disjoint unions?

Inclusions preserve lex structure, etc.?

# Functors and nat trans

See: ambient/category_old.py

Most functors would have to be defined as macros (one for objects,
another for morphisms, another for equalities).
In the case of limit domain, it seems the syntax is the same for
object, morphisms and equalities. The meta types Obj, Mor, Eq apply
here. Defining a macro is simply defining a morphism in the meta
logic. Functoriality (as well as naturality, extranaturality,
monadicity, etc.) is the result of several macros, which provide
the require proofs. Functors are not fundamental. The syntax
requires macros without any assumption of functoriality.
The concept of transformation allows treating certain macros
as if they were morphisms (a kind of syntax sugar).

What about functor strength? Would a strength macro also be needed?

# Monads

The syntax sugar for Monads does need to require monadicity, it
can just follow preferred precedence (just like with +, * for
associativity, etc.).