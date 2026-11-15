$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/isqrt_NewtonMethod_sqrtqtvc: the integer Newton-method square-root
  verification condition establishes the square-bracketing specification
  through its base cases and iterative descent invariant. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain. NTP4VCTDiv is signed
  integer division truncated toward zero and is explicitly defined to return
  zero when the divisor is zero. NTP4VCSqr and NTP4VCIsqrtSpec are
  definitional renderings of the source square and integer-square-root
  specification. NTP4VCNewton is the source Newton update.

  NTP4VCInit substitutes the source let-bound initial approximation, and
  NTP4VCStep expands the proposition-valued conditional into exhaustive
  guarded cases. The final declaration similarly expands the two outer
  conditionals. These rewrites are bidirectionally equivalent to the source
  conditionals, while the quantified iterate retains its full integer domain.
  Splitting the typed parameter and nonnegativity assumption into scoped
  essential hypotheses is equivalent to the source theorem context.

  The pinned Why3 source uses integer division in every Newton update. The
  official Lean and Isabelle exports confirm the truncating quotient reading
  with Int.tdiv and cdiv. The official Rocq export instead spells the same
  positions with Z.rem, which is a substantively different operation and is
  not used here.
  The final declaration is Metamath's native unproved $a statement encoding,
  and this database contains no artifact-level $p proof declaration.
$)

$c
  NTP4VCTDiv NTP4VCSqr NTP4VCIsqrtSpec
  NTP4VCNewton NTP4VCInit NTP4VCStep
$.

ntp4vc-tdiv-syntax $a class ( NTP4VCTDiv A B ) $.
ntp4vc-sqr-syntax $a class ( NTP4VCSqr A ) $.
ntp4vc-isqrt-spec-syntax $a wff ( NTP4VCIsqrtSpec A B ) $.
ntp4vc-newton-syntax $a class ( NTP4VCNewton A B ) $.
ntp4vc-init-syntax $a wff ( NTP4VCInit A ) $.
ntp4vc-step-syntax $a wff ( NTP4VCStep A B ) $.

ntp4vc-tdiv-definition $a |- (
  NTP4VCTDiv A B
) = if (
  B = 0 ,
  0 ,
  if (
    ( A / B ) < 0 ,
    ( |^ ` ( A / B ) ) ,
    ( |_ ` ( A / B ) )
  )
) $.

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

ntp4vc-newton-definition $a |- (
  NTP4VCNewton A B
) = (
  NTP4VCTDiv
    ( ( NTP4VCTDiv A B ) + B )
    2
) $.

ntp4vc-init-definition $a |- (
  ( NTP4VCInit A )
  <->
  (
    0 < ( NTP4VCTDiv ( 1 + A ) 2 )
    /\
    (
      0 < A
      /\
      (
        ( NTP4VCTDiv ( 1 + A ) 2 )
        =
        ( NTP4VCNewton A A )
        /\
        (
          A < ( NTP4VCSqr ( A + 1 ) )
          /\
          A
          <
          (
            NTP4VCSqr
              ( ( NTP4VCTDiv ( 1 + A ) 2 ) + 1 )
          )
        )
      )
    )
  )
) $.

ntp4vc-step-definition $a |- (
  ( NTP4VCStep A B )
  <->
  (
    (
      0 < ( NTP4VCNewton A B )
      /\
      (
        0 < B
        /\
        (
          A < ( NTP4VCSqr ( B + 1 ) )
          /\
          A < ( NTP4VCSqr ( ( NTP4VCNewton A B ) + 1 ) )
        )
      )
    )
    ->
    (
      (
        ( NTP4VCNewton A B ) < B
        /\
        (
          ( NTP4VCNewton A B ) =/= 0
          /\
          (
            2 =/= 0
            /\
            (
              (
                0 <_ B
                /\
                ( NTP4VCNewton A B ) < B
              )
              /\
              (
                0 < ( NTP4VCNewton A ( NTP4VCNewton A B ) )
                /\
                (
                  0 < ( NTP4VCNewton A B )
                  /\
                  (
                    A
                    <
                    ( NTP4VCSqr ( ( NTP4VCNewton A B ) + 1 ) )
                    /\
                    A
                    <
                    (
                      NTP4VCSqr
                        (
                          ( NTP4VCNewton A ( NTP4VCNewton A B ) )
                          + 1
                        )
                    )
                  )
                )
              )
            )
          )
        )
      )
      \/
      (
        -. ( NTP4VCNewton A B ) < B
        /\
        ( NTP4VCIsqrtSpec A B )
      )
    )
  )
) $.

${
  $d y A $.

  $( Source parameter A=x; y is the universally quantified loop iterate. $)

  ntp4vc-x-integer $e |- A e. ZZ $.
  ntp4vc-x-nonnegative $e |- 0 <_ A $.

  ntp4vc-pearl-isqrt-newton-method-sqrt-vc $a |- (
    (
      A = 0
      /\
      ( NTP4VCIsqrtSpec A 0 )
    )
    \/
    (
      A =/= 0
      /\
      (
        (
          A <_ 3
          /\
          ( NTP4VCIsqrtSpec A 1 )
        )
        \/
        (
          -. A <_ 3
          /\
          (
            2 =/= 0
            /\
            (
              ( NTP4VCInit A )
              /\
              A. y e. ZZ ( NTP4VCStep A y )
            )
          )
        )
      )
    )
  ) $.
$}
