$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.axiom_gcd_aux_body_O
  (logipedia__metamath__gcd.axiom_gcd_aux_body_O), catalog title
  "gcd.axiom_gcd_aux_body_O": the zero-indexed gcd auxiliary body is the
  binary function on natural numbers that returns its first argument. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogGcdAuxBody represents the source constant of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. The nested
  maps-to term is exactly the source lambda m, n |-> m. Thus ordinary SetMM
  equality below is the source connectives.equal at the binary-function
  type. The declaration is an unproved $a statement encoding; this database
  contains no $p proof declaration.
$)

$c
  LogGcdAuxBody LogNatBinaryFunction LogNatToBinaryFunction
$.

log-gcd-aux-body-syntax $a class ( LogGcdAuxBody ) $.
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

  logipedia-gcd-axiom-gcd-aux-body-o $a |-
    (
      ( LogGcdAuxBody ) e. ( LogNatToBinaryFunction )
      /\
      ( ( LogGcdAuxBody ) ` 0 ) =
        ( m e. NN0 |-> ( n e. NN0 |-> m ) )
    )
  $.
$}
