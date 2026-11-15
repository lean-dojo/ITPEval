$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_leb_body_O (logipedia__metamath__nat.eq_leb_body_O), catalog title
  "nat.eq_leb_body_O": the less-than-or-equal Boolean computation body at
  natural zero is Leibniz equal, as a function from natural numbers to
  Booleans, to the constant-true Boolean function. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  LogLebBody represents the fixed source constant of type

    NN0 -> NN0 -> {0,1}.

  LogNatBoolUnaryFunction and LogNatBoolBinaryFunction explicitly encode the
  full source function spaces. The maps-to term preserves the source lambda
  over every natural m, with Boolean true represented by 1. A predicate on
  the unary-function carrier is represented extensionally by a subset p of
  that carrier. Universal transport of membership from leb_body O to the
  constant-true function is exactly the source definition of
  leibniz.leibniz at the function type. Every declaration is an unproved $a
  statement encoding; this artifact introduces no $p proof declaration.
$)

$c
  LogLebBody LogNatBoolUnaryFunction LogNatBoolBinaryFunction
$.

log-leb-body-syntax $a class ( LogLebBody ) $.
log-nat-bool-unary-function-syntax $a
  class ( LogNatBoolUnaryFunction )
$.
log-nat-bool-binary-function-syntax $a
  class ( LogNatBoolBinaryFunction )
$.

log-nat-bool-unary-function-definition $a |-
  ( LogNatBoolUnaryFunction ) = ( { 0 , 1 } ^m NN0 )
$.

log-nat-bool-binary-function-definition $a |-
  ( LogNatBoolBinaryFunction ) =
    ( ( LogNatBoolUnaryFunction ) ^m NN0 )
$.

${
  $d m p $.

  logipedia-nat-eq-leb-body-o $a |-
    (
      ( LogLebBody ) e. ( LogNatBoolBinaryFunction )
      /\
      (
        ( m e. NN0 |-> 1 ) e. ( LogNatBoolUnaryFunction )
        /\
        A. p e. ~P ( LogNatBoolUnaryFunction )
          (
            ( ( LogLebBody ` 0 ) e. p )
            ->
            ( ( m e. NN0 |-> 1 ) e. p )
          )
      )
    )
  $.
$}
