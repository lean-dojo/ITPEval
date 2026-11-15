$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.sym_eq_invert_permut_body_O
  (logipedia__metamath__permutation.sym_eq_invert_permut_body_O), catalog
  title "permutation.sym_eq_invert_permut_body_O": the functional that
  returns zero after testing whether its natural-number argument equals the
  input function at zero is Leibniz equal to the zero-indexed
  invert_permut body. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogInvertPermutBody represents the fixed source constant of type

    NN0 -> (NN0 -> NN0) -> NN0 -> NN0.

  LogNatUnaryFunction is the full carrier NN0 -> NN0, LogNatFunctional is
  the full curried carrier (NN0 -> NN0) -> NN0 -> NN0, and
  LogNatToFunctional is the full type of LogInvertPermutBody. The nested
  maps-to term retains the source lambdas over f and m. The SetMM
  conditional retains the source term match_bool_type NN0 0 0
  (eqb m (f 0)); both branches are zero exactly as in the source.

  A predicate on LogNatFunctional is represented extensionally by a subset
  p of that carrier. Universal transport of membership from the nested
  maps-to term to LogInvertPermutBody at zero is therefore exactly the
  source definition of leibniz.leibniz at the full functional type. All
  declarations are unproved $a statement encodings; this artifact adds no
  $p proof declaration.
$)

$c
  LogInvertPermutBody LogNatUnaryFunction LogNatFunctional
  LogNatToFunctional
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
  $d f m p $.

  logipedia-permutation-sym-eq-invert-permut-body-o $a |-
    (
      ( LogInvertPermutBody ) e. ( LogNatToFunctional )
      /\
      A. p e. ~P ( LogNatFunctional )
        (
          (
            (
              f e. ( LogNatUnaryFunction ) |->
                (
                  m e. NN0 |->
                    if (
                      m = ( f ` 0 ) ,
                      0 ,
                      0
                    )
                )
            )
            e.
            p
          )
          ->
          ( ( ( LogInvertPermutBody ) ` 0 ) e. p )
        )
    )
  $.
$}
