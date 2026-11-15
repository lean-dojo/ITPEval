$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1357684
  (thousand-theorems__metamath__Q1357684), "Riesz representation theorem":
  on every complete real or complex inner-product space, the canonical map
  from a vector to its inner-product functional is a conjugate-linear
  isometric equivalence with the bounded linear dual. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's CHil class consists of complete real or complex inner-product
  spaces. For W in CHil, W NMHom ( ringLMod ` ( Scalar ` W ) ) is the space
  of bounded linear functionals on W. SetMM's inner product is linear in its
  first slot, opposite to mathlib's convention, so ( y ( .i ` W ) x )
  faithfully renders mathlib's inner product inner x y.

  The displayed map is therefore exactly InnerProductSpace.toDual. Its
  explicit inner-product definition supplies conjugate linearity, while the
  two asserted properties say that it is bijective onto the continuous dual
  and preserves the norm. Together these are the source conjugate-linear
  isometric equivalence. The final declaration is the single unproved corpus
  $a statement; this root statement file contains no $p proof statement.
$)

${
  $d W x y $.

  thousand-theorems-q1357684-riesz-representation $a |-
    A. W e. CHil
      (
        (
          x e. ( Base ` W )
            |->
          (
            y e. ( Base ` W )
              |->
            ( y ( .i ` W ) x )
          )
        )
        :
        ( Base ` W )
        -1-1-onto->
        (
          W
          NMHom
          ( ringLMod ` ( Scalar ` W ) )
        )
        /\
        A. x e. ( Base ` W )
          (
            (
              W
              normOp
              ( ringLMod ` ( Scalar ` W ) )
            )
            `
            (
              (
                x e. ( Base ` W )
                  |->
                (
                  y e. ( Base ` W )
                    |->
                  ( y ( .i ` W ) x )
                )
              )
              `
              x
            )
          )
          =
          ( ( norm ` W ) ` x )
      )
  $.
$}
