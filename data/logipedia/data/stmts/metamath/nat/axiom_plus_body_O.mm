$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_plus_body_O
  (logipedia__metamath__nat.axiom_plus_body_O), catalog title
  "nat.axiom_plus_body_O": the natural-number addition body at zero is the
  identity function on natural numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogPlusBody represents the fixed source constant of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried natural-number function spaces. The maps-to term preserves the
  source lambda over every natural m. Native SetMM equality is bidirectionally
  equivalent to connectives.equal here: equal_leibniz yields native equality,
  while native equality rewrites the right side to the left and refl_equal
  supplies source reflexivity. All declarations are unproved $a statement
  encodings; this database contains no $p proof declaration.
$)

$c LogPlusBody LogNatUnaryFunction LogNatBinaryFunction $.

log-plus-body-syntax $a class ( LogPlusBody ) $.
log-nat-unary-function-syntax $a class ( LogNatUnaryFunction ) $.
log-nat-binary-function-syntax $a class ( LogNatBinaryFunction ) $.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( LogNatUnaryFunction ) ^m NN0 )
$.

${
  logipedia-nat-axiom-plus-body-o $a |-
    (
      ( LogPlusBody ) e. ( LogNatBinaryFunction )
      /\
      (
        ( m e. NN0 |-> m ) e. ( LogNatUnaryFunction )
        /\
        ( LogPlusBody ` 0 ) = ( m e. NN0 |-> m )
      )
    )
  $.
$}
