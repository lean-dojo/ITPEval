$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_b2: a finite sum of ratios of binomial coefficients equals
  a closed rational expression when r, s, and t are nonnegative integers
  with r + s at most t. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the class of nonnegative integers, 0 ... s is the inclusive
  interval from 0 through s, _C is the binomial coefficient operation, and
  sum_ is finite summation. Division is complex division; because all
  numerator and denominator terms are natural numbers, this is the canonical
  rational-valued interpretation used by the Lean and Rocq sources. Under the
  stated inequality, the natural subtractions t - s and t + 1 - s agree with
  ordinary integer subtraction.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d i r s t $.

  putnambench-putnam-1987-b2 $a |-
    A. r e. NN0
      A. s e. NN0
        A. t e. NN0
          (
            ( r + s ) <_ t
            ->
            (
              sum_ i e. ( 0 ... s )
                (
                  ( s _C i )
                  /
                  ( t _C ( r + i ) )
                )
            )
            =
            (
              ( t + 1 )
              /
              (
                ( ( t + 1 ) - s )
                x.
                ( ( t - s ) _C r )
              )
            )
          )
  $.
$}
