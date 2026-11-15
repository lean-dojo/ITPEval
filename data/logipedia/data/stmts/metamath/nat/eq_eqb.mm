$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_eqb (logipedia__metamath__nat.eq_eqb), catalog title "nat.eq_eqb":
  for every natural number, eqb at that number is Leibniz equal to
  filter_nat_type applied to eqb_body at the same number, as functions from
  naturals to Booleans. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogEqb and LogEqbBody represent the fixed source constants of type

    NN0 -> NN0 -> {0,1}.

  LogFilterNatTypeNatBool represents nat.filter_nat_type specialized to
  results of type NN0 -> {0,1}, with type

    (NN0 -> NN0 -> {0,1}) -> NN0 -> NN0 -> {0,1}.

  LogNatBoolUnaryFunction and LogNatBoolBinaryFunction explicitly encode
  those curried function spaces. A predicate on the unary-function carrier
  is represented extensionally by a subset p of that carrier. Universal
  transport of membership from eqb n to the filtered eqb_body value is
  exactly the source definition of leibniz.leibniz at the function type.
  Every declaration introduced by this artifact is an unproved $a statement
  encoding; this artifact adds no $p proof declaration.
$)

$c
  LogEqb LogEqbBody LogFilterNatTypeNatBool
  LogNatBoolUnaryFunction LogNatBoolBinaryFunction
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

log-nat-bool-unary-function-definition $a |-
  ( LogNatBoolUnaryFunction ) = ( { 0 , 1 } ^m NN0 )
$.

log-nat-bool-binary-function-definition $a |-
  ( LogNatBoolBinaryFunction ) =
    ( ( LogNatBoolUnaryFunction ) ^m NN0 )
$.

${
  $d n p $.

  logipedia-nat-eq-eqb $a |-
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
          A. p e. ~P ( LogNatBoolUnaryFunction )
            (
              ( ( ( LogEqb ) ` n ) e. p )
              ->
              (
                (
                  (
                    ( LogFilterNatTypeNatBool )
                    `
                    ( LogEqbBody )
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
