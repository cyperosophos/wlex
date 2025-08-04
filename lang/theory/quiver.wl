
spec BasicQuiver;
type Node;
type Edge;

fn source, target: Edge -> Node;

spec Quiver;
type Q0 <- BasicQuiver;
type Q1 <- BasicQuiver with
    Node = Q0.Edge;

fn source_globular_cond: Q0.source @ (Q1.source == Q1.target);
fn target_globular_cond: Q0.target @ (Q1.source == Q1.target);
