$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_b3: characterization of the real initial values for which the
  sequence u(0) = a, u(n+1) = 2u(n) - n^2 remains positive at every
  nonnegative integer index. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The natural-number domain is NN0, and u is quantified as an arbitrary
  total function from NN0 to RR. The source solution set is inlined as its
  explicit defining condition 3 <= a, given by the Rocq source and the
  solution annotations in the Lean and Isabelle sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a n u $.

  putnambench-putnam-1980-b3 $a |- A. a e. RR A. u
    (
      (
        (
          u : NN0 --> RR
          /\
          (
            ( u ` 0 ) = a
            /\
            A. n e. NN0
              ( u ` ( n + 1 ) )
              =
              (
                ( 2 x. ( u ` n ) )
                -
                ( n ^ 2 )
              )
          )
        )
        ->
        (
          A. n e. NN0 0 < ( u ` n )
          <->
          3 <_ a
        )
      )
    )
  $.
$}
