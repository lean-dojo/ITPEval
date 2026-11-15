$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_a1: the possible sums of squares of a positive real sequence
  with prescribed positive total are exactly the reals strictly between zero
  and the square of that total. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is the class of all real-valued sequences indexed by the
  nonnegative integers. The two sum_ expressions are set.mm's unbounded
  real-series sums, matching the total infinite sums in the source
  formalizations. The sequence witness remains internally existentially
  quantified for each possible value S.

  The right side inlines the explicit Rocq solution and the open-interval
  solution annotated in the Lean and Isabelle sources. The final declaration
  is the single unproved $a corpus statement; this database contains no $p
  proof statement.
$)

${
  $d A S j x $.

  putnambench-putnam-2000-a1 $a |- A. A e. RR
    (
      0 < A
      ->
      {
        S e. RR |
        E. x e. ( RR ^m NN0 )
          (
            (
              A. j e. NN0
                0 < ( x ` j )
            )
            /\
            (
              (
                sum_ j e. NN0
                  ( x ` j )
              )
              =
              A
              /\
              (
                sum_ j e. NN0
                  ( ( x ` j ) ^ 2 )
              )
              =
              S
            )
          )
      }
      =
      {
        S e. RR |
        (
          0 < S
          /\
          S < ( A ^ 2 )
        )
      }
    )
  $.
$}
