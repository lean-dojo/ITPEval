$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_a3: the probability that no prefix sum of a uniformly ordered
  permutation of 1 through 3k+1 is divisible by three has the stated
  factorial closed form. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive k, Base ` SymGrp ` (1 ... (3k+1)) is the finite set of all
  orders of the integers 1 through 3k+1. The restricted class in the
  numerator consists exactly of those orders for which every nonempty prefix
  sum has nonzero remainder modulo 3. Since all entries are positive, this is
  equivalent to excluding positive prefix sums divisible by 3.

  The quotient of the two finite cardinalities is therefore the uniform
  probability in the problem, and the right side is

                 k! (k+1)!
             ------------------- .
             (3k+1) (2k)!

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f i k m $.

  putnambench-putnam-2007-a3 $a |- A. k e. NN
    (
      (
        #
        `
        {
          f e. ( Base ` ( SymGrp ` ( 1 ... ( ( 3 x. k ) + 1 ) ) ) ) |
          A. m e. ( 1 ... ( ( 3 x. k ) + 1 ) )
            (
              (
                sum_ i e. ( 1 ... m )
                  ( f ` i )
              )
              mod 3
            )
            =/= 0
        }
      )
      /
      (
        #
        `
        ( Base ` ( SymGrp ` ( 1 ... ( ( 3 x. k ) + 1 ) ) ) )
      )
      =
      (
        (
          ( ! ` k )
          x.
          ( ! ` ( k + 1 ) )
        )
        /
        (
          ( ( 3 x. k ) + 1 )
          x.
          ( ! ` ( 2 x. k ) )
        )
      )
    )
  $.
$}
