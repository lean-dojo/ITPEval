$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_minus_body_O (logipedia__metamath__nat.eq_minus_body_O), catalog
  title "nat.eq_minus_body_O": the natural-number subtraction body at zero is
  Leibniz equal, as a function on natural numbers, to the constant-zero
  function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogMinusBody represents the fixed source constant of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried natural-number function spaces. The maps-to term preserves the
  source lambda over every natural m and returns natural zero. A predicate on
  the unary-function carrier is represented extensionally by a subset p of
  that carrier. Universal transport of membership from minus_body 0 to the
  constant-zero function is exactly the source definition of
  leibniz.leibniz at the function type. Every assertion introduced by this
  artifact is an unproved $a statement encoding; this artifact introduces no
  $p proof declaration.
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

${
  $d m p $.

  logipedia-nat-eq-minus-body-o $a |-
    (
      ( LogMinusBody ) e. ( LogNatBinaryFunction )
      /\
      (
        ( m e. NN0 |-> 0 ) e. ( LogNatUnaryFunction )
        /\
        A. p e. ~P ( LogNatUnaryFunction )
          (
            ( ( LogMinusBody ` 0 ) e. p )
            ->
            ( ( m e. NN0 |-> 0 ) e. p )
          )
      )
    )
  $.
$}
