$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_107 (verina__metamath__verina_basic_107), catalog title
  ComputeAvg: the exact executable program floor-divides the sum of two
  integers by two and satisfies its Euclidean quotient-remainder correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. VERINAB107Pre is the source True
  precondition together with the two Int input types.

  For positive divisor two, floor of SetMM rational division is exactly
  Lean's Euclidean integer quotient, including for negative sums.
  VERINAB107ComputeAvg is therefore the exact source executable expression
  (a + b) / 2. SetMM integer remainder modulo positive two is likewise
  Lean's nonnegative remainder, so VERINAB107Post preserves the source
  equality 2 * result = a + b - ((a + b) % 2).

  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB107Pre VERINAB107ComputeAvg VERINAB107Post
$.

verinab107-precondition-syntax
  $a wff ( VERINAB107Pre A B ) $.
verinab107-program-syntax
  $a class ( VERINAB107ComputeAvg A B ) $.
verinab107-postcondition-syntax
  $a wff ( VERINAB107Post A B C ) $.

verinab107-precondition-definition $a |- (
  VERINAB107Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab107-program-definition $a |- (
  VERINAB107ComputeAvg A B
) = (
  |_ ` ( ( A + B ) / 2 )
) $.

verinab107-postcondition-definition $a |- (
  VERINAB107Post A B C
) <-> (
  (
    (
      A e. ZZ
      /\
      B e. ZZ
    )
    /\
    C e. ZZ
  )
  /\
  (
    ( 2 x. C )
    =
    (
      ( A + B )
      -
      ( ( A + B ) mod 2 )
    )
  )
) $.

verina-basic-107-compute-avg $a |- A. a e. ZZ A. b e. ZZ
  (
    ( VERINAB107Pre a b )
    ->
    (
      VERINAB107Post
        a
        b
        ( VERINAB107ComputeAvg a b )
    )
  )
$.
