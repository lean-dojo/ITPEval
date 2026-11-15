$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/sf_HoareLogic_reduce_to_zeroqtvc: the reduce-to-zero Hoare-logic
  verification condition states invariant initialization, variant decrease,
  invariant preservation, and the zero-valued loop exit over unbounded
  integers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full unbounded integer domain. A is the source input x,
  and y is the source loop state x1, internally universally quantified over
  all integers. The source parameter type and precondition fact0 are retained
  as scoped essential hypotheses.

  The proposition-valued source conditional on y being nonzero is expanded
  into two exhaustive guarded branches. This is bidirectionally equivalent
  to the source if-then-else. The repeated nonnegativity facts, subtraction,
  strict variant decrease, invariant-preservation obligation, exit equality,
  conjunction nesting, and quantifier scope are preserved without
  simplification. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d y A $.

  $( Source theorem parameter A=x and its precondition fact0. $)

  ntp4vc-reduce-to-zero-x-integer
    $e |- A e. ZZ $.

  ntp4vc-reduce-to-zero-x-nonnegative
    $e |- 0 <_ A $.

  ntp4vc-pearl-sf-hoarelogic-reduce-to-zero-vc $a |- (
    0 <_ A
    /\
    A. y e. ZZ
      (
        0 <_ y
        ->
        (
          (
            y =/= 0
            /\
            (
              (
                0 <_ y
                /\
                ( y - 1 ) < y
              )
              /\
              0 <_ ( y - 1 )
            )
          )
          \/
          (
            -. y =/= 0
            /\
            y = 0
          )
        )
      )
  ) $.
$}
