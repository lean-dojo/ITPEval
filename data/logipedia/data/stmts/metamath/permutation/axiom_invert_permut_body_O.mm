$(
  Statement-only formalization of the Logipedia corpus artifact
  permutation.axiom_invert_permut_body_O
  (logipedia__metamath__permutation.axiom_invert_permut_body_O), catalog
  title "permutation.axiom_invert_permut_body_O": the zero-indexed
  invert_permut body equals the functional that returns zero after testing
  whether its natural-number argument equals the input function at zero.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogInvertPermutBody represents the fixed source constant of type

    NN0 -> (NN0 -> NN0) -> NN0 -> NN0.

  LogNatUnaryFunction is the full carrier NN0 -> NN0, LogNatFunctional is
  the full curried carrier (NN0 -> NN0) -> NN0 -> NN0, and
  LogNatToFunctional is the full type of LogInvertPermutBody. The SetMM
  conditional retains the source term match_bool_type NN0 0 0
  (eqb m (f 0)); both branches are zero exactly as in the source.

  Native SetMM equality is bidirectionally equivalent to connectives.equal
  here: equal_leibniz yields native equality, while native equality rewrites
  the right side to the left and refl_equal supplies source reflexivity. All
  declarations are unproved $a statement encodings; this database contains
  no $p proof declaration.
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
  $d f m $.

  logipedia-permutation-axiom-invert-permut-body-o $a |-
    (
      ( LogInvertPermutBody ) e. ( LogNatToFunctional )
      /\
      ( ( LogInvertPermutBody ) ` 0 ) =
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
    )
  $.
$}
