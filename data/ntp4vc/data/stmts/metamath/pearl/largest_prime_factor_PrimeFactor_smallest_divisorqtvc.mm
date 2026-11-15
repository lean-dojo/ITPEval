$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/largest_prime_factor_PrimeFactor_smallest_divisorqtvc: the
  smallest-divisor verification condition checks the direct-return and
  recursive branches, including descent, divisibility, and absence of any
  smaller divisor over the integers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain. A and B are respectively
  the Why3 parameters n and d. The scoped essential hypotheses reproduce the
  four generated-VC assumptions, including the full integer quantifier in the
  no-smaller-divisor premise.

  The pinned Why3 source uses mach.int.Int remainder in the test n % d = 0.
  Since the assumptions force n and d to be positive, SetMM's A mod B is
  exactly that truncating remainder at this occurrence. The secondary Rocq
  export places the quotient in this test; that export defect does not
  override the pinned source.

  Each source Boolean conditional is rendered as its two exhaustive guarded
  cases. In particular, universally quantifying the uniquely determined
  Boolean test value and then assuming it is not true is equivalent to the
  implication from the negated test used below. Likewise, the existential
  Boolean in the result antecedent is expanded into its true and false
  guarded branches. Expanding these guards recovers the original let,
  conditional, existential, and universal scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  artifact-level $p declaration.
$)

${
  $d i r A B $.

  ntp4vc-n-integer $e |- A e. ZZ $.
  ntp4vc-d-integer $e |- B e. ZZ $.
  ntp4vc-fact0 $e |- 2 <_ A $.
  ntp4vc-fact1 $e |- 2 <_ B $.
  ntp4vc-fact2 $e |- B <_ A $.
  ntp4vc-fact3 $e |- A. i e. ZZ
    (
      (
        2 <_ i
        /\
        i < B
      )
      ->
      -. ( i || A )
    ) $.

  ntp4vc-pearl-largest-prime-factor-smallest-divisor-vc $a |- (
    (
      -. A < ( B x. B )
      ->
      (
        (
          2 <_ B
          ->
          B =/= 0
        )
        /\
        (
          -. (
            2 <_ B
            /\
            ( A mod B ) = 0
          )
          ->
          (
            (
              0 <_ ( A - B )
              /\
              ( A - ( B + 1 ) ) < ( A - B )
            )
            /\
            (
              2 <_ A
              /\
              (
                (
                  2 <_ ( B + 1 )
                  /\
                  ( B + 1 ) <_ A
                )
                /\
                A. i e. ZZ
                  (
                    (
                      2 <_ i
                      /\
                      i < ( B + 1 )
                    )
                    ->
                    -. ( i || A )
                  )
              )
            )
          )
        )
      )
    )
    /\
    A. r e. ZZ
      (
        (
          (
            A < ( B x. B )
            /\
            r = A
          )
          \/
          (
            -. A < ( B x. B )
            /\
            (
              (
                (
                  2 <_ B
                  /\
                  ( A mod B ) = 0
                )
                /\
                r = B
              )
              \/
              (
                -. (
                  2 <_ B
                  /\
                  ( A mod B ) = 0
                )
                /\
                (
                  (
                    ( B + 1 ) <_ r
                    /\
                    r <_ A
                  )
                  /\
                  (
                    r || A
                    /\
                    A. i e. ZZ
                      (
                        (
                          2 <_ i
                          /\
                          i < r
                        )
                        ->
                        -. ( i || A )
                      )
                  )
                )
              )
            )
          )
        )
        ->
        (
          (
            B <_ r
            /\
            r <_ A
          )
          /\
          (
            r || A
            /\
            A. i e. ZZ
              (
                (
                  2 <_ i
                  /\
                  i < r
                )
                ->
                -. ( i || A )
              )
          )
        )
      )
  ) $.
$}
