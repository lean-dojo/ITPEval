$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_a2: a nonzero real sequence satisfying a quadratic
  determinant identity obeys a second-order linear recurrence with a
  constant real coefficient. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is the class of all real-valued sequences indexed by the
  nonnegative integers. Quantification over NN is exactly quantification over
  the source indices n >= 1, so n - 1 remains in the sequence domain.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a n x $.

  putnambench-putnam-1993-a2 $a |- A. x e. ( RR ^m NN0 )
    (
      (
        A. n e. NN0
          ( x ` n ) =/= 0
        /\
        A. n e. NN
          (
            (
              ( x ` n ) ^ 2
              -
              (
                ( x ` ( n - 1 ) )
                x.
                ( x ` ( n + 1 ) )
              )
            )
            =
            1
          )
      )
      ->
      E. a e. RR
        A. n e. NN
          ( x ` ( n + 1 ) )
          =
          (
            (
              a
              x.
              ( x ` n )
            )
            -
            ( x ` ( n - 1 ) )
          )
    )
  $.
$}
