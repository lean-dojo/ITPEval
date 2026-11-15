$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.axiom_invert_permut
  (logipedia__metamath__permutation.axiom_invert_permut), catalog title
  "permutation.axiom_invert_permut": for every natural number, the source
  equality predicate relates invert_permut at that number to filter_nat_type
  applied to invert_permut_body at the same number, as functionals from
  natural-number endofunctions to natural-number endofunctions. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  LogInvertPermut and LogInvertPermutBody represent the fixed source
  constants of type

    NN0 -> (NN0 -> NN0) -> NN0 -> NN0.

  LogNatUnaryFunction is the full carrier NN0 -> NN0, and
  LogNatFunctional is the full curried source result type

    (NN0 -> NN0) -> NN0 -> NN0.

  LogFilterNatTypeFunctional represents nat.filter_nat_type specialized to
  that result type. LogConnectivesEqual remains the source's opaque
  polymorphic equality predicate, specialized in the final statement to
  LogNatFunctional. The membership conjuncts preserve every source
  declaration's full function type. All declarations are unproved $a
  statement encodings; this database contains no $p proof declaration.
$)

$c
  LogInvertPermut LogInvertPermutBody LogFilterNatTypeFunctional
  LogNatUnaryFunction LogNatFunctional LogNatToFunctional
  LogConnectivesEqual
$.

log-invert-permut-syntax $a class ( LogInvertPermut ) $.
log-invert-permut-body-syntax $a class ( LogInvertPermutBody ) $.
log-filter-nat-type-functional-syntax $a
  class ( LogFilterNatTypeFunctional )
$.
log-nat-unary-function-syntax $a
  class ( LogNatUnaryFunction )
$.
log-nat-functional-syntax $a
  class ( LogNatFunctional )
$.
log-nat-to-functional-syntax $a
  class ( LogNatToFunctional )
$.
log-connectives-equal-syntax $a wff
  LogConnectivesEqual A B C
$.

log-nat-unary-function-definition $a |-
  ( LogNatUnaryFunction ) = ( NN0 ^m NN0 )
$.

log-nat-functional-definition $a |-
  ( LogNatFunctional ) =
    (
      ( LogNatUnaryFunction )
      ^m
      ( LogNatUnaryFunction )
    )
$.

log-nat-to-functional-definition $a |-
  ( LogNatToFunctional ) =
    ( ( LogNatFunctional ) ^m NN0 )
$.

${
  logipedia-permutation-axiom-invert-permut $a |-
    (
      (
        ( LogInvertPermut ) e. ( LogNatToFunctional )
        /\
        ( LogInvertPermutBody ) e. ( LogNatToFunctional )
      )
      /\
      (
        ( LogFilterNatTypeFunctional ) e.
          (
            ( LogNatToFunctional )
            ^m
            ( LogNatToFunctional )
          )
        /\
        A. n e. NN0
          LogConnectivesEqual
            ( LogNatFunctional )
            ( ( LogInvertPermut ) ` n )
            (
              (
                ( LogFilterNatTypeFunctional )
                `
                ( LogInvertPermutBody )
              )
              `
              n
            )
      )
    )
  $.
$}
