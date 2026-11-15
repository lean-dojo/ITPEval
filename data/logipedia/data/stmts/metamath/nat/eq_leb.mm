$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_leb (logipedia__metamath__nat.eq_leb), catalog title "nat.eq_leb":
  for every natural number, leb at that number is Leibniz equal to
  filter_nat_type applied to leb_body at the same number, as functions from
  naturals to Booleans. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLeb and LogLebBody represent the fixed source constants of type

    NN0 -> NN0 -> {0,1}.

  LogFilterNatTypeNatBool represents nat.filter_nat_type specialized to
  results of type NN0 -> {0,1}, with type

    (NN0 -> NN0 -> {0,1}) -> NN0 -> NN0 -> {0,1}.

  LogNatBoolUnaryFunction and LogNatBoolBinaryFunction explicitly encode
  those curried function spaces. A predicate on the unary-function carrier
  is represented extensionally by a subset p of that carrier. Universal
  transport of membership from leb n to the filtered leb_body value is
  exactly the source definition of leibniz.leibniz at the function type.
  Every declaration introduced by this artifact is an unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

$c
  LogLeb LogLebBody LogFilterNatTypeNatBool
  LogNatBoolUnaryFunction LogNatBoolBinaryFunction
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

log-nat-bool-unary-function-definition $a |-
  ( LogNatBoolUnaryFunction ) = ( { 0 , 1 } ^m NN0 )
$.

log-nat-bool-binary-function-definition $a |-
  ( LogNatBoolBinaryFunction ) =
    ( ( LogNatBoolUnaryFunction ) ^m NN0 )
$.

${
  $d n p $.

  logipedia-nat-eq-leb $a |-
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
          A. p e. ~P ( LogNatBoolUnaryFunction )
            (
              ( ( ( LogLeb ) ` n ) e. p )
              ->
              (
                (
                  (
                    ( LogFilterNatTypeNatBool )
                    `
                    ( LogLebBody )
                  )
                  `
                  n
                )
                e.
                p
              )
            )
      )
    )
  $.
$}
