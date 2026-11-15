$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.eq_div_aux_body_O
  (logipedia__metamath__div_mod.eq_div_aux_body_O), catalog title
  "div_mod.eq_div_aux_body_O": the zero-indexed division auxiliary body is
  Leibniz equal to the constant-zero binary function on natural numbers.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogDivAuxBody represents the source constant of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogNatBinaryFunction is the curried function space NN0 -> NN0 -> NN0,
  and LogNatToBinaryFunction is NN0 -> LogNatBinaryFunction. The nested
  maps-to term is exactly the source lambda m, n |-> 0. A predicate on the
  binary-function type is represented extensionally by a subset q. Therefore
  the bounded universal implication is exactly the source definition of
  leibniz.leibniz in its stated direction. Every declaration is an unproved
  $a statement encoding; this database contains no $p proof declaration.
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
  $d m n q $.

  logipedia-div-mod-eq-div-aux-body-o $a |-
    (
      (
        ( LogDivAuxBody ) e. ( LogNatToBinaryFunction )
        /\
        ( m e. NN0 |-> ( n e. NN0 |-> 0 ) ) e.
          ( LogNatBinaryFunction )
      )
      /\
      A. q e. ~P ( LogNatBinaryFunction )
        (
          ( ( LogDivAuxBody ) ` 0 ) e. q
          ->
          ( m e. NN0 |-> ( n e. NN0 |-> 0 ) ) e. q
        )
    )
  $.
$}
