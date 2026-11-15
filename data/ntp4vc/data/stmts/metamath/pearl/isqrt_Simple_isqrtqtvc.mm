$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/isqrt_Simple_isqrtqtvc: the simple integer-square-root verification
  condition establishes its initialization facts and preserves the
  square-bounding invariant across each loop step. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain. NTP4VCSqr and
  NTP4VCIsqrtSpec are definitional renderings of the source square and
  integer-square-root specification.

  NTP4VCIsqrtSimpleStep expands the proposition-valued source conditional
  into exhaustive guarded cases. This is bidirectionally equivalent to the
  source conditional, and the loop counter retains its full integer
  quantifier domain. Splitting the typed parameter and nonnegativity
  assumption into scoped essential hypotheses is equivalent to the source
  theorem context. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c NTP4VCSqr NTP4VCIsqrtSpec NTP4VCIsqrtSimpleStep $.

ntp4vc-sqr-syntax $a class ( NTP4VCSqr A ) $.
ntp4vc-isqrt-spec-syntax $a wff ( NTP4VCIsqrtSpec A B ) $.
ntp4vc-isqrt-simple-step-syntax
  $a wff ( NTP4VCIsqrtSimpleStep A B ) $.

ntp4vc-sqr-definition $a |- (
  NTP4VCSqr A
) = ( A x. A ) $.

ntp4vc-isqrt-spec-definition $a |- (
  ( NTP4VCIsqrtSpec A B )
  <->
  (
    0 <_ B
    /\
    (
      ( NTP4VCSqr B ) <_ A
      /\
      A < ( NTP4VCSqr ( B + 1 ) )
    )
  )
) $.

ntp4vc-isqrt-simple-step-definition $a |- (
  ( NTP4VCIsqrtSimpleStep A B )
  <->
  (
    (
      0 <_ B
      /\
      ( NTP4VCSqr B ) <_ A
    )
    ->
    (
      (
        ( NTP4VCSqr ( B + 1 ) ) <_ A
        /\
        (
          (
            0 <_ ( A - B )
            /\
            ( A - ( B + 1 ) ) < ( A - B )
          )
          /\
          (
            0 <_ ( B + 1 )
            /\
            (
              ( NTP4VCSqr ( B + 1 ) ) <_ A
              /\
              (
                ( NTP4VCSqr ( B + 1 ) )
                +
                ( ( 2 x. ( B + 1 ) ) + 1 )
              )
              =
              ( NTP4VCSqr ( ( B + 1 ) + 1 ) )
            )
          )
        )
      )
      \/
      (
        -. ( NTP4VCSqr ( B + 1 ) ) <_ A
        /\
        ( NTP4VCIsqrtSpec A B )
      )
    )
  )
) $.

${
  $d y A $.

  $( Source parameter A=x; y is the universally quantified loop counter. $)

  ntp4vc-x-integer $e |- A e. ZZ $.
  ntp4vc-x-nonnegative $e |- 0 <_ A $.

  ntp4vc-pearl-isqrt-simple-isqrt-vc $a |- (
    0 <_ 0
    /\
    (
      ( NTP4VCSqr 0 ) <_ A
      /\
      (
        1 = ( NTP4VCSqr ( 0 + 1 ) )
        /\
        A. y e. ZZ ( NTP4VCIsqrtSimpleStep A y )
      )
    )
  ) $.
$}
