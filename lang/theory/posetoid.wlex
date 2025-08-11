from quiver import BasicQuiver;

spec Posetoid;
type Q <- BasicQuiver;
type El := Q.Node;
type Rel := Q.Edge;
fn source := Q.source;
fn target := Q.target;

type Path := {
    f: Rel, g: Rel,
    source @ $f == target @ $g,
};
    
fn ref: ($, $) @ El -> (source, target);
fn trans: (source @ $g, target @ $f) @ Path
    -> (source, target);

spec Setoid;
type P <- Posetoid;
type Eq := P.Rel;
fn source := P.source;
fn target := P.target;
fn sym: (source, target) -> (target, source);

spec Congruence;
type S <- Setoid;
type Eq := S.Eq;
fn source := S.source;
fn target := S.target;
fn eq := (source, target);
fn unique: (
    d, e: Eq,
    eq @ ($d == $e),
) -> ($, $) @ Eq;