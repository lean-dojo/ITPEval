$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_a5: the product of sin(a_i)/a_i for finitely many real
  numbers in (0, pi) is bounded by the corresponding power at their
  arithmetic mean. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is SetMM's class of positive natural numbers, so 1 ... n is a
  nonempty n-element index set. The class RR ^m ( 1 ... n ) contains
  every real-valued family on that set. This presentation is carried to
  Lean's Fin n family and Rocq's length-n sequence by their canonical
  index bijections, which preserve the finite sum and product.

  The equality defining m states that it is the arithmetic mean. Since
  n is positive, summing a_i / n as in the Lean and Rocq sources equals
  dividing the finite sum by n as in the Isabelle source and below.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a i m n $.

  putnambench-putnam-1978-a5 $a |-
    A. n e. NN
    A. a e. ( RR ^m ( 1 ... n ) )
    A. m e. RR
      (
        (
          A. i e. ( 1 ... n )
            (
              0 < ( a ` i )
              /\
              ( a ` i ) < _pi
            )
          /\
          m =
            (
              (
                sum_ i e. ( 1 ... n )
                  ( a ` i )
              )
              /
              n
            )
        )
        ->
        (
          prod_ i e. ( 1 ... n )
            (
              ( sin ` ( a ` i ) )
              /
              ( a ` i )
            )
        )
        <_
        (
          (
            ( sin ` m )
            /
            m
          )
          ^
          n
        )
      )
  $.
$}
