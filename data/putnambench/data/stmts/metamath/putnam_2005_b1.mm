$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_b1: the nonzero real polynomial
  (y - 2x)(y - 2x - 1) vanishes at (floor(a), floor(2a)) for every
  real number a. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's RR is the real-number class and |_ is the standard floor
  function. The displayed polynomial is the explicit solution documented
  by the Lean, Isabelle, and Rocq sources. Its nonzeroness is expressed
  extensionally by the existence of a real input where its value is
  nonzero, followed by the required universal vanishing statement.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a x y $.

  putnambench-putnam-2005-b1 $a |-
    (
      E. x e. RR E. y e. RR
        (
          (
            y
            -
            ( 2 x. x )
          )
          x.
          (
            (
              y
              -
              ( 2 x. x )
            )
            -
            1
          )
        )
        =/=
        0
      /\
      A. a e. RR
        (
          (
            ( |_ ` ( 2 x. a ) )
            -
            ( 2 x. ( |_ ` a ) )
          )
          x.
          (
            (
              ( |_ ` ( 2 x. a ) )
              -
              ( 2 x. ( |_ ` a ) )
            )
            -
            1
          )
        )
        =
        0
    )
  $.
$}
