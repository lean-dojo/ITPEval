$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.axiom_gcd_aux (logipedia__metamath__gcd.axiom_gcd_aux), catalog title
  "gcd.axiom_gcd_aux": for every natural number p, the source equality
  predicate relates gcd_aux p to filter_nat_type applied to gcd_aux_body at p
  as binary natural-number functions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogGcdAux and LogGcdAuxBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogFilterNatTypeBin represents nat.filter_nat_type specialized to binary
  natural-number functions, with type

    (NN0 -> NN0 -> NN0) family -> NN0 -> (NN0 -> NN0 -> NN0).

  LogConnectivesEqual remains the source's opaque polymorphic equality
  predicate, specialized in the final statement to the binary-function
  carrier. The function-space membership conjuncts preserve the source
  declarations' types. All declarations are unproved $a statement encodings;
  this database contains no $p proof declaration.
$)

$c
  LogGcdAux LogGcdAuxBody LogFilterNatTypeBin
  LogNatBinaryFunction LogNatToBinaryFunction LogConnectivesEqual
$.

log-gcd-aux-syntax $a class ( LogGcdAux ) $.
log-gcd-aux-body-syntax $a class ( LogGcdAuxBody ) $.
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
  logipedia-gcd-axiom-gcd-aux $a |-
    (
      (
        ( LogGcdAux ) e. ( LogNatToBinaryFunction )
        /\
        ( LogGcdAuxBody ) e. ( LogNatToBinaryFunction )
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
            ( ( LogGcdAux ) ` p )
            (
              (
                ( LogFilterNatTypeBin )
                `
                ( LogGcdAuxBody )
              )
              `
              p
            )
      )
    )
  $.
$}
