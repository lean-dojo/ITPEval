$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_a1: every positive integer is a nonempty finite sum of terms
  2^r 3^s with nonnegative integer exponents, with no distinct summand
  dividing another. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The positive integer n and the nonempty number k of summands range over NN.
  The functions r and s assign the two NN0 exponents to each index in
  1 ... k. Pairing these two functions is definitionally equivalent to the
  source's finite function into pairs of nonnegative exponents.

  Since n is positive, the source's apparently permitted empty family cannot
  satisfy the displayed sum equality, so requiring k in NN is equivalent.
  The nested restricted universal quantifiers state the directed
  nondivisibility condition for every pair of distinct indices exactly.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i j k n r s $.

  putnambench-putnam-2005-a1 $a |- A. n e. NN
    E. k e. NN
      E. r e. ( NN0 ^m ( 1 ... k ) )
        E. s e. ( NN0 ^m ( 1 ... k ) )
          (
            n
            =
            sum_ i e. ( 1 ... k )
              (
                ( 2 ^ ( r ` i ) )
                x.
                ( 3 ^ ( s ` i ) )
              )
            /\
            A. i e. ( 1 ... k )
              A. j e. ( 1 ... k )
                (
                  i =/= j
                  ->
                  -.
                  (
                    (
                      ( 2 ^ ( r ` i ) )
                      x.
                      ( 3 ^ ( s ` i ) )
                    )
                    ||
                    (
                      ( 2 ^ ( r ` j ) )
                      x.
                      ( 3 ^ ( s ` j ) )
                    )
                  )
                )
          )
  $.
$}
