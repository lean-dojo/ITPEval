$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_b2: for positive integers m at most n, n divides the product
  of gcd(m,n) and the binomial coefficient n choose m. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers, _C is its binomial-coefficient
  operation, gcd is integer greatest common divisor, and || is integer
  divisibility. Thus the restricted binders encode 1 <= m <= n directly.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d m n $.

  putnambench-putnam-2000-b2 $a |-
    A. m e. NN
      A. n e. NN
        (
          m <_ n
          ->
          n || ( ( m gcd n ) x. ( n _C m ) )
        )
  $.
$}
