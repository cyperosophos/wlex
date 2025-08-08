from quiver import Quiver;
from posetoid import Posetoid, Congruence;

spec Category;
type Q <- Quiver;
type P <- Posetoid with
    Q = Q.Q0;
type S <- Congruence with
    S.P.Q = Q.Q1;
type Obj := P.El;
type Mor := P.Rel;
type Eq := S.Eq;
fn eq := S.eq;
fn source := P.source;
fn target := P.target;
type Composable := P.Path;
fn identity := P.ref;
fn compose := P.trans;

# TODO: Use @> and <@ to disambiguate composition of pairings?
fn left_identity_law := (compose @ (identity @ target, $), $) @ Mor -> eq;
fn right_identity_law := (compose @ ($, identity @ source), $) @ Mor -> eq;
fn associativity := (
    compose @ ($f, compose @ ($g, $h)),
    compose @ (compose @ ($f, $g), $h),
) @ (
    Composable,
    (g, h): Composable,
) -> eq;

type ComposableEq := (
    d, e: Eq,
    source @ S.source @ $d == target @ S.target @ $e,
);

fn compose_eq: compose @ (S.source, S.target) @ ComposableEq -> eq;