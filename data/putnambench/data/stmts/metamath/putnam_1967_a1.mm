$(
  Statement-only formalization of PutnamBench artifact putnam_1967_a1:
  the coefficient-weighted sum bound for a finite real sine polynomial whose
  absolute value is bounded pointwise by the absolute value of sin(x). This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  The positive integer n is represented as a nonnegative integer together
  with the explicit hypothesis 0 < n. The coefficient function A is a total
  real sequence, but only its values on the inclusive interval 1 ... n occur,
  which is equivalent to the finite coefficient domain in the source. The
  function F and its defining equality are retained explicitly.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A F i n x $.

  putnambench-putnam-1967-a1 $a |- A. n e. NN0
    A. A A. F
      (
        (
          (
            (
              0 < n
              /\
              A : NN0 --> RR
            )
            /\
            (
              F : RR --> RR
              /\
              F =
                (
                  x e. RR |->
                    sum_ i e. ( 1 ... n )
                      (
                        ( A ` i )
                        x.
                        ( sin ` ( i x. x ) )
                      )
                )
            )
          )
          /\
          A. x e. RR
            ( abs ` ( F ` x ) ) <_ ( abs ` ( sin ` x ) )
        )
        ->
        (
          abs
          `
          (
            sum_ i e. ( 1 ... n )
              ( i x. ( A ` i ) )
          )
        )
        <_
        1
      )
  $.
$}
