$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.eq_mod_aux (logipedia__metamath__div_mod.eq_mod_aux), catalog title
  "div_mod.eq_mod_aux": for every natural number p, Leibniz equality relates
  the binary-natural function mod_aux p to the result of filtering
  mod_aux_body at p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogModAux and LogModAuxBody represent the source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogFilterNatTypeBin is nat.filter_nat_type specialized to the result type
  NN0 -> NN0 -> NN0. A predicate on the binary-function carrier is represented
  extensionally by a subset q. Thus transport of membership from mod_aux p to
  the filtered function for every q is exactly the source definition of
  leibniz.leibniz at that function type. The explicit SetMM function-space
  declarations preserve all source types. Every declaration is an unproved
  $a statement encoding; this database contains no $p proof declaration.
$)

$c
  LogModAux LogModAuxBody LogFilterNatTypeBin
  LogNatBinaryFunction LogNatToBinaryFunction
$.

log-mod-aux-syntax $a class ( LogModAux ) $.
log-mod-aux-body-syntax $a class ( LogModAuxBody ) $.
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

  logipedia-div-mod-eq-mod-aux $a |-
    (
      (
        ( LogModAux ) e. ( LogNatToBinaryFunction )
        /\
        ( LogModAuxBody ) e. ( LogNatToBinaryFunction )
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
              ( ( LogModAux ) ` p ) e. q
              ->
              ( ( ( LogFilterNatTypeBin ) ` ( LogModAuxBody ) ) ` p ) e. q
            )
      )
    )
  $.
$}
