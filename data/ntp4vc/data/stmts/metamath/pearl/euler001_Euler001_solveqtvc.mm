$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/euler001_Euler001_solveqtvc: the Euler 1 verification condition
  expresses the sum of all nonnegative integers below n divisible by 3 or 5
  through the inclusion-exclusion closed formula. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A is the source integer n, and B is the source total integer function
  sum_multiple_3_5_lt. Its empty, nonmultiple, and multiple recurrence laws
  are retained as scoped essential hypotheses.

  NTP4VCTDiv is integer division truncated toward zero for the positive
  divisors used here. It is the Why3 division operation rendered as Lean
  Int.tdiv and Isabelle cdiv. NTP4VCQ3, NTP4VCQ5, and NTP4VCQ15 expand the
  three source let-bindings, and NTP4VCClosed expands the final
  inclusion-exclusion expression and its division by 2.

  Moving the source parameter typing, fact0, and imported recurrence laws
  into scoped essential hypotheses is equivalent to their theorem context.
  The final declaration preserves the four explicit nonzero conjuncts and
  the closed-form equality. It is Metamath's native unproved $a statement
  encoding; this database contains no artifact-level $p declaration.
$)

$c
  NTP4VCTDiv NTP4VCQ3 NTP4VCQ5 NTP4VCQ15 NTP4VCClosed
$.

ntp4vc-tdiv-syntax $a class ( NTP4VCTDiv A B ) $.
ntp4vc-q3-syntax $a class ( NTP4VCQ3 A ) $.
ntp4vc-q5-syntax $a class ( NTP4VCQ5 A ) $.
ntp4vc-q15-syntax $a class ( NTP4VCQ15 A ) $.
ntp4vc-closed-syntax $a class ( NTP4VCClosed A ) $.

ntp4vc-tdiv-definition $a |- (
  NTP4VCTDiv A B
) = if (
  A < 0 ,
  ( |^ ` ( A / B ) ) ,
  ( |_ ` ( A / B ) )
) $.

ntp4vc-q3-definition $a |- (
  NTP4VCQ3 A
) = (
  NTP4VCTDiv ( A - 1 ) 3
) $.

ntp4vc-q5-definition $a |- (
  NTP4VCQ5 A
) = (
  NTP4VCTDiv ( A - 1 ) 5
) $.

ntp4vc-q15-definition $a |- (
  NTP4VCQ15 A
) = (
  NTP4VCTDiv ( A - 1 ) ; 1 5
) $.

ntp4vc-closed-definition $a |- (
  NTP4VCClosed A
) = (
  NTP4VCTDiv
    (
      (
        (
          ( 3 x. ( NTP4VCQ3 A ) )
          x.
          ( ( NTP4VCQ3 A ) + 1 )
        )
        +
        (
          ( 5 x. ( NTP4VCQ5 A ) )
          x.
          ( ( NTP4VCQ5 A ) + 1 )
        )
      )
      -
      (
        ( ; 1 5 x. ( NTP4VCQ15 A ) )
        x.
        ( ( NTP4VCQ15 A ) + 1 )
      )
    )
    2
) $.

${
  $d k A $.
  $d k B $.

  $( Source parameters: A=n and B=sum_multiple_3_5_lt. $)

  ntp4vc-n-integer $e |- A e. ZZ $.
  ntp4vc-n-at-least-one $e |- 1 <_ A $.
  ntp4vc-sum-function $e |- B e. ( ZZ ^m ZZ ) $.

  ntp4vc-sum-empty $e |- ( B ` 0 ) = 0 $.

  ntp4vc-sum-no $e |- A. k e. ZZ
    (
      (
        0 <_ k
        /\
        (
          ( k mod 3 ) =/= 0
          /\
          ( k mod 5 ) =/= 0
        )
      )
      ->
      ( B ` ( k + 1 ) ) = ( B ` k )
    ) $.

  ntp4vc-sum-yes $e |- A. k e. ZZ
    (
      (
        0 <_ k
        /\
        (
          ( k mod 3 ) = 0
          \/
          ( k mod 5 ) = 0
        )
      )
      ->
      ( B ` ( k + 1 ) ) = ( ( B ` k ) + k )
    ) $.

  ntp4vc-pearl-euler001-solve-vc $a |- (
    3 =/= 0
    /\
    (
      5 =/= 0
      /\
      (
        ; 1 5 =/= 0
        /\
        (
          2 =/= 0
          /\
          ( NTP4VCClosed A ) = ( B ` A )
        )
      )
    )
  ) $.
$}
