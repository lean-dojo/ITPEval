$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_minus_body_O
  (logipedia__metamath__nat.axiom_minus_body_O), catalog title
  "nat.axiom_minus_body_O": the natural-number subtraction body at zero
  equals the constant-zero function on all natural numbers. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogMinusBody represents the fixed source constant of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried natural-number function spaces. The maps-to term preserves the
  source lambda over every natural m and returns natural zero.

  Native SetMM equality is bidirectionally equivalent to connectives.equal
  here: equal_leibniz yields native equality, while native equality rewrites
  the right side to the left and refl_equal supplies source reflexivity.
  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c LogMinusBody LogNatUnaryFunction LogNatBinaryFunction $.

log-minus-body-syntax $a class ( LogMinusBody ) $.
log-nat-unary-function-syntax $a
  class ( LogNatUnaryFunction )
$.
log-nat-binary-function-syntax $a
  class ( LogNatBinaryFunction )
$.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( LogNatUnaryFunction ) ^m NN0 )
$.

logipedia-nat-axiom-minus-body-o $a |-
  (
    ( LogMinusBody ) e. ( LogNatBinaryFunction )
    /\
    ( ( LogMinusBody ` 0 ) = ( m e. NN0 |-> 0 ) )
  )
$.
