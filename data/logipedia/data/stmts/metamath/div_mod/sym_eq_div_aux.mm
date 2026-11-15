$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.sym_eq_div_aux
  (logipedia__metamath__div_mod.sym_eq_div_aux), catalog title
  "div_mod.sym_eq_div_aux": for every natural number p, Leibniz equality
  relates the result of filtering div_aux_body at p to the binary-natural
  function div_aux p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogDivAux and LogDivAuxBody represent the source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogFilterNatTypeBin is nat.filter_nat_type specialized to the result type
  NN0 -> NN0 -> NN0. A predicate on the binary-function carrier is represented
  extensionally by a subset q. Thus transport of membership from the filtered
  function to div_aux p for every q is exactly the source definition of
  leibniz.leibniz at that function type. The explicit SetMM function-space
  declarations preserve all source types. Every declaration is an unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

$c
  LogDivAux LogDivAuxBody LogFilterNatTypeBin
  LogNatBinaryFunction LogNatToBinaryFunction
$.

log-div-aux-syntax $a class ( LogDivAux ) $.
log-div-aux-body-syntax $a class ( LogDivAuxBody ) $.
log-filter-nat-type-bin-syntax $a class ( LogFilterNatTypeBin ) $.
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
  $d p q $.

  logipedia-div-mod-sym-eq-div-aux $a |-
    (
      (
        ( LogDivAux ) e. ( LogNatToBinaryFunction )
        /\
        ( LogDivAuxBody ) e. ( LogNatToBinaryFunction )
      )
      /\
      (
        ( LogFilterNatTypeBin ) e.
          (
            ( LogNatToBinaryFunction )
            ^m
            ( LogNatToBinaryFunction )
          )
        /\
        A. p e. NN0
          A. q e. ~P ( LogNatBinaryFunction )
            (
              ( ( ( LogFilterNatTypeBin ) ` ( LogDivAuxBody ) ) ` p ) e. q
              ->
              ( ( LogDivAux ) ` p ) e. q
            )
      )
    )
  $.
$}
