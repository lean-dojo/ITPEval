$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_a4: among 19 positive integers at most 93 and 93 positive
  integers at most 19, a nonempty subset of the first family and a subset
  of the second family have equal sums. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carriers 0 ... 18 and 0 ... 92 contain exactly 19 and 93 indices.
  Quantifying x and y over integer-valued functions on these carriers,
  together with the displayed positive bounds, is equivalent to the
  positive-natural-valued source formulations. The witnesses S and T are
  internally existential subsets of the respective carriers; S is nonempty,
  while T is unrestricted as in the source statements.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d S T i j x y $.

  putnambench-putnam-1993-a4 $a |-
    A. x e. ( ZZ ^m ( 0 ... ; 1 8 ) )
    A. y e. ( ZZ ^m ( 0 ... ; 9 2 ) )
      (
        (
          A. i e. ( 0 ... ; 1 8 )
            (
              0 < ( x ` i )
              /\
              ( x ` i ) <_ ; 9 3
            )
          /\
          A. j e. ( 0 ... ; 9 2 )
            (
              0 < ( y ` j )
              /\
              ( y ` j ) <_ ; 1 9
            )
        )
        ->
        E. S e. { S e. ~P ( 0 ... ; 1 8 ) | S =/= (/) }
        E. T e. ~P ( 0 ... ; 9 2 )
          (
            sum_ i e. S ( x ` i )
          )
          =
          (
            sum_ j e. T ( y ` j )
          )
      )
  $.
$}
