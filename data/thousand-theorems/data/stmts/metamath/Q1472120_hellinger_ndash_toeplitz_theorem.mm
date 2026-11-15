$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1472120
  (thousand-theorems__metamath__Q1472120), "Hellinger&ndash;Toeplitz theorem":
  every everywhere-defined symmetric linear operator on a complete real or
  complex inner-product space is continuous. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's CHil class consists of complete inner-product spaces over the real
  or complex numbers. For w in CHil, w LMHom w is the class of all
  everywhere-defined linear endomorphisms of w.

  SetMM's inner product is linear in its first slot, opposite to mathlib's
  convention. Thus ( y ( .i ` W ) ( T ` x ) ) renders mathlib's inner product
  of T x with y, and ( ( T ` y ) ( .i ` W ) x ) renders the inner product of
  x with T y. The displayed identity is therefore exactly
  LinearMap.IsSymmetric T. Membership in
  ( ( TopOpen ` W ) Cn ( TopOpen ` W ) ) is continuity for the norm topology.
  The final declaration is the single unproved corpus $a statement; this root
  file contains no $p proof statement.
$)

${
  $d t w x y $.

  thousand-theorems-q1472120-hellinger-toeplitz $a |-
    A. w e. CHil
      A. t e. ( w LMHom w )
        (
          (
            A. x e. ( Base ` w )
              A. y e. ( Base ` w )
                (
                  ( y ( .i ` w ) ( t ` x ) )
                  =
                  ( ( t ` y ) ( .i ` w ) x )
                )
          )
          ->
          t e. ( ( TopOpen ` w ) Cn ( TopOpen ` w ) )
        )
  $.
$}
