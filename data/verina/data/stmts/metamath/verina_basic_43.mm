$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_43
  (verina__metamath__verina_basic_43), catalog title
  sumOfFourthPowerOfOddNumbers: the exact natural-number recursion sums the
  fourth powers of the first n odd numbers and satisfies its closed-form
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain. For n in NN0, 0 ..^ n is
  exactly the index set { 0, ..., n - 1 }, and finite summation uses the same
  natural addition as the Lean program.

  VERINAB43SumOfFourthPowerOfOddNumbers is the finite fold
    sum_{k < n} (2*k + 1)^4.
  This is definitionally equivalent to the source match recursion: the empty
  sum is zero at n = 0, and extending the range from n to n + 1 adds exactly
  (2*n + 1)^4. Thus it fixes the exact executable result independently of the
  postcondition and admits no additional outputs.

  VERINAB43NatSub is Lean's truncated natural subtraction.
  VERINAB43Pre preserves the source True precondition together with the Nat
  input type. VERINAB43Post preserves the source Nat result type and the exact
  left-associated natural-subtraction formula
    15 * result =
      n * (2*n + 1) * (((7 + 24*n^3) - 12*n^2) - 14*n).
  The proof-valued precondition arguments to the implementation and
  postcondition have no computational or propositional effect beyond the
  explicit antecedent in the final correctness assertion. Every earlier $a
  is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB43NatSub VERINAB43Pre
  VERINAB43SumOfFourthPowerOfOddNumbers VERINAB43Post
$.

verinab43-nat-sub-syntax
  $a class ( VERINAB43NatSub A B ) $.
verinab43-precondition-syntax
  $a wff ( VERINAB43Pre A ) $.
verinab43-program-syntax
  $a class ( VERINAB43SumOfFourthPowerOfOddNumbers A ) $.
verinab43-postcondition-syntax
  $a wff ( VERINAB43Post A B ) $.

verinab43-nat-sub-definition $a |- (
  VERINAB43NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab43-precondition-definition $a |- (
  VERINAB43Pre A
) <-> (
  A e. NN0
) $.

${
  $d k A $.

  verinab43-program-definition $a |- (
    VERINAB43SumOfFourthPowerOfOddNumbers A
  ) = (
    sum_ k e. ( 0 ..^ A )
      (
        (
          ( ; 2 x. k ) + 1
        ) ^ 4
      )
  ) $.
$}

verinab43-postcondition-definition $a |- (
  VERINAB43Post A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    ( ; 1 5 x. B )
    =
    (
      (
        A
        x.
        ( ( ; 2 x. A ) + 1 )
      )
      x.
      (
        VERINAB43NatSub
          (
            VERINAB43NatSub
              (
                7
                +
                ( ; 2 4 x. ( A ^ 3 ) )
              )
              ( ; 1 2 x. ( A ^ 2 ) )
          )
          ( ; 1 4 x. A )
      )
    )
  )
) $.

verina-basic-43-sum-of-fourth-power-of-odd-numbers $a |-
  A. n e. NN0
    (
      ( VERINAB43Pre n )
      ->
      (
        VERINAB43Post
          n
          ( VERINAB43SumOfFourthPowerOfOddNumbers n )
      )
    )
$.
