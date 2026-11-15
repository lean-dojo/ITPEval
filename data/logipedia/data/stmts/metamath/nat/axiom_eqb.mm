$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_eqb (logipedia__metamath__nat.axiom_eqb), catalog title
  "nat.axiom_eqb": for every natural number, the source equality predicate
  relates eqb at that number to filter_nat_type applied to eqb_body at the
  same number, as functions from naturals to Booleans. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  LogEqb and LogEqbBody represent the fixed source constants of type

    NN0 -> NN0 -> {0,1}.

  LogFilterNatTypeNatBool represents nat.filter_nat_type specialized to
  results of type NN0 -> {0,1}, with type

    (NN0 -> NN0 -> {0,1}) -> NN0 -> NN0 -> {0,1}.

  LogNatBoolUnaryFunction and LogNatBoolBinaryFunction explicitly encode
  those curried function spaces. LogConnectivesEqual remains the source's
  opaque polymorphic equality predicate, specialized in the final statement
  to the full function type NN0 -> {0,1}. The membership conjuncts preserve
  the source declarations' types. All declarations are unproved $a statement
  encodings; this database contains no $p proof declaration.
$)

$c
  LogEqb LogEqbBody LogFilterNatTypeNatBool
  LogNatBoolUnaryFunction LogNatBoolBinaryFunction
  LogConnectivesEqual
$.

log-eqb-syntax $a class ( LogEqb ) $.
log-eqb-body-syntax $a class ( LogEqbBody ) $.
log-filter-nat-type-nat-bool-syntax $a
  class ( LogFilterNatTypeNatBool )
$.
log-nat-bool-unary-function-syntax $a
  class ( LogNatBoolUnaryFunction )
$.
log-nat-bool-binary-function-syntax $a
  class ( LogNatBoolBinaryFunction )
$.
log-connectives-equal-syntax $a wff
  LogConnectivesEqual A B C
$.

log-nat-bool-unary-function-definition $a |-
  ( LogNatBoolUnaryFunction ) = ( { 0 , 1 } ^m NN0 )
$.

log-nat-bool-binary-function-definition $a |-
  ( LogNatBoolBinaryFunction ) =
    ( ( LogNatBoolUnaryFunction ) ^m NN0 )
$.

${
  logipedia-nat-axiom-eqb $a |-
    (
      (
        ( LogEqb ) e. ( LogNatBoolBinaryFunction )
        /\
        ( LogEqbBody ) e. ( LogNatBoolBinaryFunction )
      )
      /\
      (
        ( LogFilterNatTypeNatBool ) e.
          (
            ( LogNatBoolBinaryFunction )
            ^m
            ( LogNatBoolBinaryFunction )
          )
        /\
        A. n e. NN0
          LogConnectivesEqual
            ( LogNatBoolUnaryFunction )
            ( ( LogEqb ) ` n )
            (
              (
                ( LogFilterNatTypeNatBool )
                `
                ( LogEqbBody )
              )
              `
              n
            )
      )
    )
  $.
$}
