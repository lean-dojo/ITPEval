$(
  Statement-only formalization of PutnamBench artifact putnam_1962_b1:
  the binomial addition identity for real falling factorials defined by
  finite products over consecutive nonnegative integers. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The included set.mm library supplies real-valued function spaces,
  nonnegative and positive integers, half-open and inclusive integer
  intervals, finite products and sums, and binomial coefficients.

  The final unproved $a assertion quantifies the original family p of real
  functions, the real arguments x and y, and the nonnegative integer n. The
  half-open range ( 0 ..^ m ) is exactly the source range from 0 through
  m - 1.
$)

${
  $d P x y n m z i k $.

  putnambench-putnam-1962-b1 $a |- A. P
    A. x e. RR
    A. y e. RR
    A. n e. NN0
      (
        (
          (
            P : NN0 --> ( RR ^m RR )
            /\
            ( P ` 0 ) = ( z e. RR |-> 1 )
          )
          /\
          A. m e. NN
            ( P ` m ) =
              (
                z e. RR |->
                  prod_ i e. ( 0 ..^ m ) ( z - i )
              )
        )
        ->
        (
          ( ( P ` n ) ` ( x + y ) )
          =
          sum_ k e. ( 0 ... n )
            (
              ( n _C k )
              x.
              (
                ( ( P ` k ) ` x )
                x.
                ( ( P ` ( n - k ) ) ` y )
              )
            )
        )
      )
  $.
$}
