$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_plus_body_O
  (logipedia__metamath__nat.sym_eq_plus_body_O), catalog title
  "nat.sym_eq_plus_body_O": the identity function on natural numbers is
  Leibniz equal to the natural-number addition body at zero. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogPlusBody represents the fixed source constant of type

    NN0 -> NN0 -> NN0.

  LogNatUnaryFunction and LogNatBinaryFunction explicitly encode the source's
  curried natural-number function spaces. The maps-to term preserves the
  source lambda over every natural m. A predicate on the unary-function
  carrier is represented extensionally by a subset p of that carrier.
  Universal transport of membership from the identity function to plus_body
  O is exactly the source definition of leibniz.leibniz at the function type.
  Every declaration is an unproved $a statement encoding; this artifact
  introduces no $p proof declaration.
$)

$c LogPlusBody LogNatUnaryFunction LogNatBinaryFunction $.

log-plus-body-syntax $a class ( LogPlusBody ) $.
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

  logipedia-nat-sym-eq-plus-body-o $a |-
    (
      ( LogPlusBody ) e. ( LogNatBinaryFunction )
      /\
      (
        ( m e. NN0 |-> m ) e. ( LogNatUnaryFunction )
        /\
        A. p e. ~P ( LogNatUnaryFunction )
          (
            ( ( m e. NN0 |-> m ) e. p )
            ->
            ( ( LogPlusBody ` 0 ) e. p )
          )
      )
    )
  $.
$}
