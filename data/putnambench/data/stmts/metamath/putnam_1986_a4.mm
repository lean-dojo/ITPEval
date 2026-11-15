$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_a4: the number of n-by-n matrices over {-1, 0, 1} whose
  permutation-transversal sums are all equal has the stated exponential
  closed form for every positive integer n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier ( 1 ... n ) represents Fin n. A matrix is represented as a
  total function from the Cartesian square of this carrier to
  { -u 1 , 0 , 1 }, and a transversal is selected by a bijection p of the
  carrier. The internally existential integer S is shared by every such
  permutation, exactly expressing equality of all transversal sums.

  The right side is the source coefficient tuple (1, 4, 2, 3, -4, 2, 1)
  expanded as 4^n + 2*3^n - 4*2^n + 1. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d A S i n p $.

  putnambench-putnam-1986-a4 $a |- A. n e. NN
    (
      (
        #
        `
        {
          A e.
            (
              { -u 1 , 0 , 1 }
              ^m
              ( ( 1 ... n ) X. ( 1 ... n ) )
            )
          |
          E. S e. ZZ
            A. p
              (
                p : ( 1 ... n ) -1-1-onto-> ( 1 ... n )
                ->
                (
                  sum_ i e. ( 1 ... n )
                    ( A ` <. i , ( p ` i ) >. )
                )
                =
                S
              )
        }
      )
      =
      (
        (
          (
            ( 4 ^ n )
            +
            ( 2 x. ( 3 ^ n ) )
          )
          -
          ( 4 x. ( 2 ^ n ) )
        )
        +
        1
      )
    )
  $.
$}
