$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_leb (logipedia__metamath__nat.axiom_leb), catalog title
  "nat.axiom_leb": for every natural number, the source equality predicate
  relates leb at that number to filter_nat_type applied to leb_body at the
  same number, as functions from naturals to Booleans. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  LogLeb and LogLebBody represent the fixed source constants of type

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
  LogLeb LogLebBody LogFilterNatTypeNatBool
  LogNatBoolUnaryFunction LogNatBoolBinaryFunction
  LogConnectivesEqual
$.

log-leb-syntax $a class ( LogLeb ) $.
log-leb-body-syntax $a class ( LogLebBody ) $.
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
  logipedia-nat-axiom-leb $a |-
    (
      (
        ( LogLeb ) e. ( LogNatBoolBinaryFunction )
        /\
        ( LogLebBody ) e. ( LogNatBoolBinaryFunction )
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
            ( ( LogLeb ) ` n )
            (
              (
                ( LogFilterNatTypeNatBool )
                `
                ( LogLebBody )
              )
              `
              n
            )
      )
    )
  $.
$}
