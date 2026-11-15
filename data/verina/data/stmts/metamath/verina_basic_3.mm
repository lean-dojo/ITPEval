$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_3
  (verina__metamath__verina_basic_3), catalog title isDivisibleBy11: the exact
  executable integer remainder test returns true precisely when its input is
  divisible by eleven, with its Boolean correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and { 0 , 1 } represents Bool with
  false = 0 and true = 1. For the positive modulus eleven, SetMM's integer
  remainder agrees with Lean's Int remainder on every integer input.

  VERINAB3Pre is the source True precondition together with the Int input
  type. VERINAB3IsDivisibleBy11 is exactly the executable source program
  n % 11 == 0: it returns one exactly when the remainder is zero and zero
  otherwise, so it admits no additional outputs.

  VERINAB3Post preserves the source conjunction of implications. A true
  result requires an integer k with n = 11 * k, while a false result requires
  n to differ from 11 * k for every integer k. The proof-valued precondition
  argument is computationally and propositionally unused and is represented
  by the explicit precondition antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB3Pre VERINAB3IsDivisibleBy11 VERINAB3Post
$.

verinab3-precondition-syntax
  $a wff ( VERINAB3Pre A ) $.
verinab3-program-syntax
  $a class ( VERINAB3IsDivisibleBy11 A ) $.
verinab3-postcondition-syntax
  $a wff ( VERINAB3Post A B ) $.

verinab3-precondition-definition $a |- (
  VERINAB3Pre A
) <-> (
  A e. ZZ
) $.

verinab3-program-definition $a |- (
  VERINAB3IsDivisibleBy11 A
) = if (
  ( A mod ; 1 1 ) = 0 ,
  1 ,
  0
) $.

${
  $d k A B $.

  verinab3-postcondition-definition $a |- (
    VERINAB3Post A B
  ) <-> (
    (
      A e. ZZ
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      (
        B = 1
        ->
        E. k e. ZZ
          A = ( ; 1 1 x. k )
      )
      /\
      (
        B = 0
        ->
        A. k e. ZZ
          A =/= ( ; 1 1 x. k )
      )
    )
  ) $.
$}

verina-basic-3-is-divisible-by-11 $a |- A. n e. ZZ
  (
    ( VERINAB3Pre n )
    ->
    (
      VERINAB3Post
        n
        ( VERINAB3IsDivisibleBy11 n )
    )
  )
$.
