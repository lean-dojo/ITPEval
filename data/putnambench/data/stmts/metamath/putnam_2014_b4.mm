$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_b4: for every positive integer n, every complex zero of the
  polynomial with kth coefficient 2^(k(n-k)) is real. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers, CC is the complex plane, and
  0 ... n is the inclusive set of coefficient indices. The displayed finite
  sum is the evaluation at z of the source polynomial whose kth coefficient
  is 2 raised to k(n-k). Since k lies between 0 and n, natural subtraction
  agrees with ordinary integer subtraction in the exponent.

  The conclusion z e. RR says exactly that the arbitrary complex zero is
  real, equivalently that its imaginary part is zero. Inlining the polynomial
  by its coefficient sum is definitionally equivalent to the source
  polynomial object and preserves every root. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d k n z $.

  putnambench-putnam-2014-b4 $a |-
    A. n e. NN
      A. z e. CC
        (
          (
            sum_ k e. ( 0 ... n )
              (
                ( 2 ^ ( k x. ( n - k ) ) )
                x.
                ( z ^ k )
              )
          )
          =
          0
          ->
          z e. RR
        )
  $.
$}
