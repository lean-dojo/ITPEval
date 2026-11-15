$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.axiom_div_aux_body_O, catalog title
  "div_mod.axiom_div_aux_body_O": the zero-indexed division auxiliary body
  is the constant-zero binary function on natural numbers. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogDivAuxBody represents the source constant of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. The nested
  maps-to term is exactly the source lambda m, n |-> 0. Thus ordinary SetMM
  equality below is the source connectives.equal at the binary-function
  type. The declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c
  LogDivAuxBody LogNatBinaryFunction LogNatToBinaryFunction
$.

log-div-aux-body-syntax $a class ( LogDivAuxBody ) $.
log-nat-binary-function-syntax $a class ( LogNatBinaryFunction ) $.
log-nat-to-binary-function-syntax $a class
  ( LogNatToBinaryFunction )
$.

log-nat-binary-function-definition $a |-
  ( LogNatBinaryFunction ) =
    ( ( NN0 ^m NN0 ) ^m NN0 )
$.

log-nat-to-binary-function-definition $a |-
  ( LogNatToBinaryFunction ) =
    ( ( LogNatBinaryFunction ) ^m NN0 )
$.

${
  $d m n $.

  logipedia-div-mod-axiom-div-aux-body-o $a |-
    (
      ( LogDivAuxBody ) e. ( LogNatToBinaryFunction )
      /\
      ( ( LogDivAuxBody ) ` 0 ) =
        ( m e. NN0 |-> ( n e. NN0 |-> 0 ) )
    )
  $.
$}
