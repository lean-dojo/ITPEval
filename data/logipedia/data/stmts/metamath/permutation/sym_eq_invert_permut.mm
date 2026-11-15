$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.sym_eq_invert_permut
  (logipedia__metamath__permutation.sym_eq_invert_permut), catalog title
  "permutation.sym_eq_invert_permut": for every natural number,
  filter_nat_type applied to invert_permut_body at that number is Leibniz
  equal to invert_permut at the same number, as functionals from
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
  that result type. A predicate on LogNatFunctional is represented
  extensionally by a subset p of that carrier. Thus universal transport of
  membership from the filtered invert_permut_body value to invert_permut n
  is exactly the source definition of leibniz.leibniz at
  LogNatFunctional. All declarations are unproved $a statement encodings;
  this artifact adds no $p proof declaration.
$)

$c
  LogInvertPermut LogInvertPermutBody LogFilterNatTypeFunctional
  LogNatUnaryFunction LogNatFunctional LogNatToFunctional
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
  $d n p $.

  logipedia-permutation-sym-eq-invert-permut $a |-
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
          A. p e. ~P ( LogNatFunctional )
            (
              (
                (
                  (
                    ( LogFilterNatTypeFunctional )
                    `
                    ( LogInvertPermutBody )
                  )
                  `
                  n
                )
                e.
                p
              )
              ->
              ( ( LogInvertPermut ` n ) e. p )
            )
      )
    )
  $.
$}
