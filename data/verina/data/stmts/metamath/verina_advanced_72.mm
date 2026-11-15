$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_72 (verina__metamath__verina_advanced_72), catalog title
  singleDigitPrimeFactor: the exact nested-divisibility program returns the
  first tested factor among 2, 3, 5, and 7, or zero, together with its full
  natural-number correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain. VERINA72TestDivisor is
  membership in the source list [2, 3, 5, 7], and VERINA72Allowed is
  membership in [0, 2, 3, 5, 7].

  VERINA72Pre is the source True precondition on a typed Nat input.
  VERINA72SingleDigitPrimeFactor reproduces the source nested if-expression
  exactly, including its initial zero test and the left-to-right remainder
  tests by 2, 3, 5, and 7. Its output is therefore fixed independently of
  the postcondition.

  VERINA72Post preserves the allowed-result condition and both source
  implications. The zero-result branch tests all four candidate divisors.
  In the nonzero branch, restricted universal quantification over 0 ..^ B
  is exactly List.range B, and its implication reproduces List.all with the
  source membership guard. The proof-valued precondition arguments are
  computationally and propositionally unused and are represented by the
  explicit precondition antecedent of the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINA72TestDivisor VERINA72Allowed
  VERINA72Pre VERINA72SingleDigitPrimeFactor VERINA72Post
$.

verina72-test-divisor-syntax
  $a wff ( VERINA72TestDivisor A ) $.
verina72-allowed-syntax
  $a wff ( VERINA72Allowed A ) $.
verina72-precondition-syntax
  $a wff ( VERINA72Pre A ) $.
verina72-program-syntax
  $a class ( VERINA72SingleDigitPrimeFactor A ) $.
verina72-postcondition-syntax
  $a wff ( VERINA72Post A B ) $.

verina72-test-divisor-definition $a |- (
  VERINA72TestDivisor A
) <-> (
  A = 2
  \/
  (
    A = 3
    \/
    (
      A = 5
      \/
      A = 7
    )
  )
) $.

verina72-allowed-definition $a |- (
  VERINA72Allowed A
) <-> (
  A = 0
  \/
  ( VERINA72TestDivisor A )
) $.

verina72-precondition-definition $a |- (
  VERINA72Pre A
) <-> (
  A e. NN0
) $.

verina72-program-definition $a |- (
  VERINA72SingleDigitPrimeFactor A
) = if (
  A = 0 ,
  0 ,
  if (
    ( A mod 2 ) = 0 ,
    2 ,
    if (
      ( A mod 3 ) = 0 ,
      3 ,
      if (
        ( A mod 5 ) = 0 ,
        5 ,
        if (
          ( A mod 7 ) = 0 ,
          7 ,
          0
        )
      )
    )
  )
) $.

${
  $d x A B $.

  verina72-postcondition-definition $a |- (
    VERINA72Post A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. NN0
    )
    /\
    (
      ( VERINA72Allowed B )
      /\
      (
        (
          B = 0
          ->
          (
            A = 0
            \/
            (
              ( A mod 2 ) =/= 0
              /\
              (
                ( A mod 3 ) =/= 0
                /\
                (
                  ( A mod 5 ) =/= 0
                  /\
                  ( A mod 7 ) =/= 0
                )
              )
            )
          )
        )
        /\
        (
          B =/= 0
          ->
          (
            A =/= 0
            /\
            (
              ( A mod B ) = 0
              /\
              A. x e. ( 0 ..^ B )
                (
                  ( VERINA72TestDivisor x )
                  ->
                  ( A mod x ) =/= 0
                )
            )
          )
        )
      )
    )
  ) $.
$}

verina-advanced-72-single-digit-prime-factor
  $a |- A. n e. NN0
    (
      ( VERINA72Pre n )
      ->
      (
        VERINA72Post
          n
          ( VERINA72SingleDigitPrimeFactor n )
      )
    )
  $.
