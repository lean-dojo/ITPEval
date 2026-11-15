$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sf_HoareLogic_slow_additionqtvc: the slow-addition Hoare-logic
  verification condition states invariant initialization and universally
  quantified loop-step and exit obligations over unbounded integers. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain. A and B are the source
  parameters x and z1, while y and z are the source loop variables z and x1
  and remain internally universally quantified over all integers. The source
  parameter types and precondition fact0 are retained as scoped essential
  hypotheses.

  The proposition-valued source conditional on z being nonzero is expanded
  into two exhaustive guarded branches. This is bidirectionally equivalent
  to the source if-then-else. The invariant, variant decrease, invariant
  preservation, exit equality, conjunction nesting, arithmetic expressions,
  and quantifier scopes are preserved without simplification. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

${
  $d y z A B $.

  $( Source theorem parameters A=x and B=z1, and precondition fact0. $)

  ntp4vc-slow-addition-x-integer
    $e |- A e. ZZ $.

  ntp4vc-slow-addition-z1-integer
    $e |- B e. ZZ $.

  ntp4vc-slow-addition-x-nonnegative
    $e |- 0 <_ A $.

  ntp4vc-pearl-sf-hoarelogic-slow-addition-vc $a |- (
    0 <_ A
    /\
    A. y e. ZZ A. z e. ZZ
      (
        (
          0 <_ z
          /\
          ( y + z ) = ( B + A )
        )
        ->
        (
          (
            z =/= 0
            /\
            (
              (
                0 <_ z
                /\
                ( z - 1 ) < z
              )
              /\
              (
                0 <_ ( z - 1 )
                /\
                ( ( y + 1 ) + ( z - 1 ) ) = ( B + A )
              )
            )
          )
          \/
          (
            -. z =/= 0
            /\
            y = ( B + A )
          )
        )
      )
  ) $.
$}
