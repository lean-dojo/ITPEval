$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2001_b4: emptiness of the intersection of all positive iterate
  images of the rational map x |-> x - 1/x away from -1, 0, and 1.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  S is the set of rationals other than -1, 0, and 1, and F ranges over
  endofunctions of S satisfying the specified formula. IterComp is set.mm's
  native finite-iteration operator. Thus the final negated existential says
  that no y in S has, for every positive integer n, a preimage in S under
  the n-fold iterate of F. This is exactly emptiness of the intersection of
  the positive iterate images.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F S n x y $.

  putnambench-putnam-2001-b4 $a |- A. S
    A. F e. ( S ^m S )
      (
        (
          S = ( QQ \ { -u 1 , 0 , 1 } )
          /\
          A. x e. S
            ( F ` x ) = ( x - ( 1 / x ) )
        )
        ->
        -. E. y e. S A. n e. NN E. x e. S
          (
            (
              ( ( IterComp ` F ) ` n )
              `
              x
            )
            =
            y
          )
      )
  $.
$}
