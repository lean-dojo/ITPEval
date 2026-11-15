$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.sym_eq_mod_aux_body_O
  (logipedia__metamath__div_mod.sym_eq_mod_aux_body_O), catalog title
  "div_mod.sym_eq_mod_aux_body_O": the binary function on natural numbers
  that returns its first argument is Leibniz equal to the zero-indexed
  modulus auxiliary body. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogModAuxBody represents the source constant of type

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
  LogModAuxBody LogNatBinaryFunction LogNatToBinaryFunction
$.

log-mod-aux-body-syntax $a class ( LogModAuxBody ) $.
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

  logipedia-div-mod-sym-eq-mod-aux-body-o $a |-
    (
      (
        ( LogModAuxBody ) e. ( LogNatToBinaryFunction )
        /\
        ( m e. NN0 |-> ( n e. NN0 |-> m ) ) e.
          ( LogNatBinaryFunction )
      )
      /\
      A. q e. ~P ( LogNatBinaryFunction )
        (
          ( m e. NN0 |-> ( n e. NN0 |-> m ) ) e. q
          ->
          ( ( LogModAuxBody ) ` 0 ) e. q
        )
    )
  $.
$}
