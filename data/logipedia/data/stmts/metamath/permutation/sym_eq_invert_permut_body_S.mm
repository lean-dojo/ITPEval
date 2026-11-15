$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_S
  (logipedia__metamath__permutation.sym_eq_invert_permut_body_S), catalog
  title "permutation.sym_eq_invert_permut_body_S": for every natural number
  n, the functional that maps f and m to successor n when m equals f at
  successor n, and otherwise to invert_permut n f m, is Leibniz equal to the
  inverse-permutation body at successor n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogInvertPermut and LogInvertPermutBody represent the fixed source
  constants of type

    NN0 -> (NN0 -> NN0) -> NN0 -> NN0.

  LogNatUnaryFunction is the full carrier NN0 -> NN0, LogNatFunctional is
  the full curried carrier (NN0 -> NN0) -> NN0 -> NN0, and
  LogNatToFunctional is the full type of both source constants. The nested
  maps-to term retains the source lambdas over f and m. The SetMM
  conditional faithfully renders match_bool_type NN0 (S n)
  (invert_permut n f m) (eqb m (f (S n))), and n + 1 renders S n.

  A predicate on LogNatFunctional is represented extensionally by a subset
  p of that carrier. Universal transport of membership from the nested
  maps-to term to LogInvertPermutBody at successor n is therefore exactly
  the source definition of leibniz.leibniz at the full functional type. All
  declarations are unproved $a statement encodings; this artifact adds no
  $p proof declaration.
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
  $d f m n p $.

  logipedia-permutation-sym-eq-invert-permut-body-s $a |-
    (
      (
        ( LogInvertPermut ) e. ( LogNatToFunctional )
        /\
        ( LogInvertPermutBody ) e. ( LogNatToFunctional )
      )
      /\
      A. n e. NN0
        A. p e. ~P ( LogNatFunctional )
          (
            (
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
              e.
              p
            )
            ->
            (
              ( ( LogInvertPermutBody ) ` ( n + 1 ) )
              e.
              p
            )
          )
    )
  $.
$}
