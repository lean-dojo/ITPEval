$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1983_a4: for m = 6k - 1 with positive natural k, the alternating
  sum of the binomial coefficients m choose (3j - 1), from j = 1 through
  2k - 1, is nonzero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN, NN0, and ZZ are set.mm's positive naturals, nonnegative integers, and
  integers. The interval ( 1 ... ( ( 2 x. k ) - 1 ) ) is inclusive, _C is
  the binomial coefficient operation, and the powers of -1 give the source
  alternating signs.

  Quantifying m and S and retaining their defining equalities reproduces the
  source parameters and assumptions exactly. Positivity of the source
  natural k is expressed by k e. NN. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d S j k m $.

  putnambench-putnam-1983-a4 $a |-
    A. k e. NN
      A. m e. NN0
        A. S e. ZZ
          (
            (
              m = ( ( 6 x. k ) - 1 )
              /\
              S =
                sum_ j e. ( 1 ... ( ( 2 x. k ) - 1 ) )
                  (
                    ( ( -u 1 ) ^ ( j + 1 ) )
                    x.
                    ( m _C ( ( 3 x. j ) - 1 ) )
                  )
            )
            ->
            S =/= 0
          )
  $.
$}
