from cart import Cart;

spec Lex;
type C <- Cart;
type Obj := C.Obj;
type Mor := C.Mor
type Eq := C.Eq;
fn eq := C.eq;
fn source := C.source;
fn target := C.target;
fn compose := C.compose;

type Parallel = (
    i, j: Mor,
    (source, target) @ ($i == $j),
);
type Fork = (
    Mor, Parallel, Eq,
    source @ Parallel == target @ Mor,
    compose @ (Parallel, Mor) == eq,
);

fn equalizer: Parallel @ ($ -> Fork);

fn meqp := Mor @ equalizer @ Parallel;
type EqualizerMor := (
    Mor, Fork, Eq,
    source @ Mor @ ($ == Fork),
    target @ Mor == source @ meqp,
    (compose @ (meqp, Mor), Mor @ Fork) == eq,
);

fn equalizer_pairing: Fork @ ($ -> EqualizerMor);
fn equalizer_pairing_unique: Mor @ (equalizer_pairing, $) @ EqualizerMor -> eq;