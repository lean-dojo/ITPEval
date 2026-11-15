$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.axiom_mod_aux, catalog title "div_mod.axiom_mod_aux": for every
  natural number p, the binary-natural function mod_aux p equals the result
  of filtering mod_aux_body at p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogModAux and LogModAuxBody represent the source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogFilterNatTypeBin is nat.filter_nat_type specialized to the result type
  NN0 -> NN0 -> NN0. Thus it maps an NN0-indexed family of binary-natural
  functions to another such family. The explicit SetMM function-space
  declarations preserve these source types, and ordinary SetMM equality
  represents connectives.equal at that function type. All declarations are
  unproved $a statement encodings; this database contains no $p proof
  declaration.
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

logipedia-div-mod-axiom-mod-aux $a |-
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
        (
          ( ( LogModAux ) ` p )
          =
          ( ( ( LogFilterNatTypeBin ) ` ( LogModAuxBody ) ) ` p )
        )
    )
  )
$.
