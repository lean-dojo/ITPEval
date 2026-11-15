$(
  Statement-only formalization of the Logipedia corpus artifact
  div_mod.axiom_div_aux
  (logipedia__metamath__div_mod.axiom_div_aux), catalog title
  "div_mod.axiom_div_aux": for every natural number p, the primitive source
  equality predicate at the binary-natural-function type relates div_aux p
  to filter_nat_type applied to div_aux_body at p. The predicate retains the
  source's primitive status and is not identified with native SetMM equality.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogDivAux and LogDivAuxBody represent the source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogFilterNatTypeBin is nat.filter_nat_type specialized to the result type
  NN0 -> NN0 -> NN0. Thus it maps an NN0-indexed family of binary-natural
  functions to another such family. The explicit SetMM function-space
  declarations preserve these source types.

  LogConnectivesEqual remains the source's primitive type-indexed predicate.
  The artifact states only the source axiom at each p; the separate
  connectives.equal_leibniz theorem is intentionally not conjoined here. No
  reflexivity, transport law, or identification with native equality is
  added. All declarations are unproved $a statement encodings; this database
  contains no $p proof declaration.
$)

$c
  LogDivAux LogDivAuxBody LogFilterNatTypeBin
  LogNatBinaryFunction LogNatToBinaryFunction LogConnectivesEqual
$.

log-div-aux-syntax $a class ( LogDivAux ) $.
log-div-aux-body-syntax $a class ( LogDivAuxBody ) $.
log-filter-nat-type-bin-syntax $a class ( LogFilterNatTypeBin ) $.
log-nat-binary-function-syntax $a class ( LogNatBinaryFunction ) $.
log-nat-to-binary-function-syntax $a class
  ( LogNatToBinaryFunction )
$.
log-connectives-equal-syntax $a wff
  LogConnectivesEqual A B C
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
  logipedia-div-mod-axiom-div-aux $a |-
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
          LogConnectivesEqual
            ( LogNatBinaryFunction )
            ( ( LogDivAux ) ` p )
            (
              (
                ( LogFilterNatTypeBin )
                `
                ( LogDivAuxBody )
              )
              `
              p
            )
      )
    )
  $.
$}
