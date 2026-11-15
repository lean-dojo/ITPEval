$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_a1: no four consecutive binomial coefficients of a positive
  integer n, starting at a positive index r with r + 3 at most n, are in
  arithmetic progression. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is the class of positive integers. The two displayed equalities use
  ordinary integer differences between natural-valued binomial coefficients,
  matching the arithmetic-progression relation in the Lean and Rocq sources.
  The final declaration is the single unproved $a corpus statement.
$)

${
  $d n r $.

  putnambench-putnam-1972-a1 $a |-
    A. n e. NN
      -. E. r e. NN
        (
          ( r + 3 ) <_ n
          /\
          (
            (
              ( n _C ( r + 3 ) )
              -
              ( n _C ( r + 2 ) )
            )
            =
            (
              ( n _C ( r + 2 ) )
              -
              ( n _C ( r + 1 ) )
            )
            /\
            (
              ( n _C ( r + 2 ) )
              -
              ( n _C ( r + 1 ) )
            )
            =
            (
              ( n _C ( r + 1 ) )
              -
              ( n _C r )
            )
          )
        )
  $.
$}
