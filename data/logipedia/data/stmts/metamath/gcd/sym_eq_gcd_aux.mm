$(
  Statement-only formalization of the Logipedia corpus artifact
  gcd.sym_eq_gcd_aux (logipedia__metamath__gcd.sym_eq_gcd_aux), catalog title
  "gcd.sym_eq_gcd_aux": for every natural number p, filter_nat_type applied
  to gcd_aux_body at p is Leibniz equal to gcd_aux p as a binary
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
  universal transport of membership from the filtered gcd_aux_body value to
  gcd_aux p is exactly the source definition of leibniz.leibniz at the
  binary-function type. The source signature fixes the constants' function
  types; those typing facts are not added as theorem conjuncts. Every
  declaration is an unproved $a statement encoding; this database contains no
  $p proof declaration.
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

  logipedia-gcd-sym-eq-gcd-aux $a |-
    A. p e. NN0
      A. q e. ~P ( LogNatBinaryFunction )
        (
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
          ->
          ( ( ( LogGcdAux ) ` p ) e. q )
        )
  $.
$}
