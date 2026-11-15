$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/power_FastExponentiation_fast_exp_2qtvc: the accumulator-based fast
  exponentiation verification condition for recursive-call descent and
  preservation of the integer power result. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain. Under the source assumption
  0 <= n, Why3's computer division by the positive integer 2 is the floor of
  n / 2, and its associated remainder is SetMM's n mod 2. Every exponent in a
  constrained branch is nonnegative, so SetMM's integer power agrees with the
  source int.Power operation.

  The proposition-valued conditional in the descent obligation is expanded
  into its two exhaustive guarded cases. The result equation retains its
  nested conditional as a class-valued if-expression. These are
  bidirectionally equivalent to the source conditionals, and the universal
  result quantifier still ranges over every integer. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  artifact-level $p declaration.
$)

${
  $d r A $.  $d r B $.  $d r C $.

  $( Source theorem parameters: A=n, B=acc, and C=x. $)

  ntp4vc-n-integer $e |- A e. ZZ $.
  ntp4vc-acc-integer $e |- B e. ZZ $.
  ntp4vc-x-integer $e |- C e. ZZ $.
  ntp4vc-n-nonnegative $e |- 0 <_ A $.

  ntp4vc-pearl-power-fast-exponentiation-fast-exp-2-vc $a |- (
    (
      A =/= 0
      ->
      (
        2 =/= 0
        /\
        (
          (
            ( A mod 2 ) = 0
            /\
            (
              2 =/= 0
              /\
              (
                (
                  0 <_ A
                  /\
                  ( |_ ` ( A / 2 ) ) < A
                )
                /\
                0 <_ ( |_ ` ( A / 2 ) )
              )
            )
          )
          \/
          (
            -. ( ( A mod 2 ) = 0 )
            /\
            (
              (
                0 <_ A
                /\
                ( A - 1 ) < A
              )
              /\
              0 <_ ( A - 1 )
            )
          )
        )
      )
    )
    /\
    A. r e. ZZ
      (
        r = if (
          A = 0 ,
          B ,
          if (
            ( A mod 2 ) = 0 ,
            (
              ( ( C x. C ) ^ ( |_ ` ( A / 2 ) ) )
              x.
              B
            ) ,
            (
              ( C ^ ( A - 1 ) )
              x.
              ( C x. B )
            )
          )
        )
        ->
        r = ( ( C ^ A ) x. B )
      )
  ) $.
$}
