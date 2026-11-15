$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.axiom_invert_permut_body_S
  (logipedia__metamath__permutation.axiom_invert_permut_body_S), catalog
  title "permutation.axiom_invert_permut_body_S": for every natural number
  n, the inverse-permutation body at successor n equals the functional that
  maps f and m to successor n when m equals f at successor n, and otherwise
  to invert_permut n f m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogInvertPermut and LogInvertPermutBody represent the fixed source
  constants of type

    NN0 -> (NN0 -> NN0) -> NN0 -> NN0.

  LogNatUnaryFunction is the full carrier NN0 -> NN0, LogNatFunctional is
  the full curried carrier (NN0 -> NN0) -> NN0 -> NN0, and
  LogNatToFunctional is the full type of both source constants. The nested
  maps-to terms retain the source lambdas over f and m. The SetMM
  conditional faithfully renders match_bool_type NN0 (S n)
  (invert_permut n f m) (eqb m (f (S n))), and n + 1 renders S n.

  Native SetMM equality is bidirectionally equivalent to connectives.equal
  here: equal_leibniz yields native equality, while native equality rewrites
  the right side to the left and refl_equal supplies source reflexivity. All
  declarations are unproved $a statement encodings; this database contains
  no $p proof declaration.
$)

$c
  LogInvertPermut LogInvertPermutBody LogNatUnaryFunction
  LogNatFunctional LogNatToFunctional
$.

log-invert-permut-syntax $a
  class ( LogInvertPermut )
$.
log-invert-permut-body-syntax $a
  class ( LogInvertPermutBody )
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
  $d f m n $.

  $( Source-signature typing hypotheses for the two fixed constants. $)
  log-invert-permut-type $e |-
    ( LogInvertPermut ) e. ( LogNatToFunctional )
  $.
  log-invert-permut-body-type $e |-
    ( LogInvertPermutBody ) e. ( LogNatToFunctional )
  $.

  logipedia-permutation-axiom-invert-permut-body-s $a |-
    A. n e. NN0
      ( ( LogInvertPermutBody ) ` ( n + 1 ) ) =
        (
          f e. ( LogNatUnaryFunction ) |->
            (
              m e. NN0 |->
                if (
                  m = ( f ` ( n + 1 ) ) ,
                  ( n + 1 ) ,
                  (
                    (
                      ( LogInvertPermut ` n )
                      `
                      f
                    )
                    `
                    m
                  )
                )
            )
        )
  $.
$}
