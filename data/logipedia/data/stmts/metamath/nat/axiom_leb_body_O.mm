$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_leb_body_O (logipedia__metamath__nat.axiom_leb_body_O),
  catalog title "nat.axiom_leb_body_O": the less-than-or-equal Boolean
  computation body at natural zero equals the constant-true Boolean function
  on all natural numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLebBody represents the fixed source constant of type

    NN0 -> NN0 -> {0,1}.

  LogNatBoolUnaryFunction and LogNatBoolBinaryFunction explicitly encode the
  full source function spaces. The maps-to term preserves the source lambda
  over every natural m, with Boolean true represented by 1.

  Native SetMM equality is bidirectionally equivalent to connectives.equal
  here: equal_leibniz yields native equality, while native equality rewrites
  the right side to the left and refl_equal supplies source reflexivity.
  All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
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
  logipedia-nat-axiom-leb-body-o $a |-
    (
      ( LogLebBody ) e. ( LogNatBoolBinaryFunction )
      /\
      (
        ( m e. NN0 |-> 1 ) e. ( LogNatBoolUnaryFunction )
        /\
        ( LogLebBody ` 0 ) = ( m e. NN0 |-> 1 )
      )
    )
  $.
$}
