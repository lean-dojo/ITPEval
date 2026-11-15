$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.eq_gcd_aux (logipedia__metamath__gcd.eq_gcd_aux), catalog title
  "gcd.eq_gcd_aux": for every natural number p, gcd_aux p is Leibniz equal
  to filter_nat_type applied to gcd_aux_body at p as a binary
  natural-number function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogGcdAux and LogGcdAuxBody represent the fixed source constants of type

    NN0 -> NN0 -> NN0 -> NN0.

  LogFilterNatTypeBin represents nat.filter_nat_type specialized to binary
  natural-number functions, with type

    (NN0 -> NN0 -> NN0) family -> NN0 -> (NN0 -> NN0 -> NN0).

  LogNatBinaryFunction and LogNatToBinaryFunction explicitly encode those
  curried function spaces. A predicate on the binary-function carrier is
  represented extensionally by a subset q of LogNatBinaryFunction. Thus
  universal transport of membership from gcd_aux p to the filtered
  gcd_aux_body value is exactly the source definition of leibniz.leibniz at
  the binary-function type. Every declaration is an unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

$c
  LogGcdAux LogGcdAuxBody LogFilterNatTypeBin
  LogNatBinaryFunction LogNatToBinaryFunction
$.

log-gcd-aux-syntax $a class ( LogGcdAux ) $.
log-gcd-aux-body-syntax $a class ( LogGcdAuxBody ) $.
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

  logipedia-gcd-eq-gcd-aux $a |-
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
          A. q e. ~P ( LogNatBinaryFunction )
            (
              ( ( ( LogGcdAux ) ` p ) e. q )
              ->
              (
                (
                  (
                    ( LogFilterNatTypeBin )
                    `
                    ( LogGcdAuxBody )
                  )
                  `
                  p
                )
                e.
                q
              )
            )
      )
    )
  $.
$}
