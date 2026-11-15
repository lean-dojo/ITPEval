$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.eq_gcd_aux_body_O
  (logipedia__metamath__gcd.eq_gcd_aux_body_O), catalog title
  "gcd.eq_gcd_aux_body_O": the zero-indexed gcd auxiliary body is Leibniz
  equal to the binary function on natural numbers that returns its first
  argument. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogGcdAuxBody represents the fixed source constant of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. The nested
  maps-to term is exactly the source lambda m, n |-> m. A predicate on the
  binary-function type is represented extensionally by a subset q. Therefore
  the bounded universal implication is exactly the source definition of
  leibniz.leibniz in its stated direction. Every declaration is an unproved
  $a statement encoding; this database contains no $p proof declaration.
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
  $d m n q $.

  logipedia-gcd-eq-gcd-aux-body-o $a |-
    (
      (
        ( LogGcdAuxBody ) e. ( LogNatToBinaryFunction )
        /\
        ( m e. NN0 |-> ( n e. NN0 |-> m ) ) e.
          ( LogNatBinaryFunction )
      )
      /\
      A. q e. ~P ( LogNatBinaryFunction )
        (
          ( ( LogGcdAuxBody ) ` 0 ) e. q
          ->
          ( m e. NN0 |-> ( n e. NN0 |-> m ) ) e. q
        )
    )
  $.
$}
