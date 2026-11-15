$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_a2: the sum of the geometric means of two finite families of
  nonnegative real numbers is at most the geometric mean of their pointwise
  sums. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m ( 1 ... n ) is the class of all real-valued functions on the
  one-based n-element interval. This is in bijection with the Fin n and
  zero-based families in the ground-truth sources, and finite products are
  unchanged by that reindexing.

  Each displayed product is nonnegative, and n is positive. Therefore
  set.mm's complex-power operation ^c with exponent 1 / n is real-valued
  and equals the source nonnegative real nth-root operation, including at
  product zero. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d a b i n $.

  putnambench-putnam-2003-a2 $a |- A. n e. NN
    A. a e. ( RR ^m ( 1 ... n ) )
      A. b e. ( RR ^m ( 1 ... n ) )
        (
          A. i e. ( 1 ... n )
            (
              0 <_ ( a ` i )
              /\
              0 <_ ( b ` i )
            )
          ->
          (
            (
              (
                prod_ i e. ( 1 ... n )
                  ( a ` i )
              )
              ^c
              ( 1 / n )
            )
            +
            (
              (
                prod_ i e. ( 1 ... n )
                  ( b ` i )
              )
              ^c
              ( 1 / n )
            )
          )
          <_
          (
            (
              prod_ i e. ( 1 ... n )
                ( ( a ` i ) + ( b ` i ) )
            )
            ^c
            ( 1 / n )
          )
        )
  $.
$}
