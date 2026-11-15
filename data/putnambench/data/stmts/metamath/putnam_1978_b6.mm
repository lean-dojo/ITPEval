$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_b6: an upper bound for the square of a weighted triangular
  double sum of real array entries lying in the unit interval. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The variable a ranges over arbitrary real-valued functions on
  NN0 x NN0, represented in curried form. Quantification of m and n over
  NN exactly expresses their strict positivity. The inclusive intervals
  1 ... n and 1 ... ( m x. i ) and set.mm's finite sum notation give the
  two source sums without restricting the underlying array to a finite
  table.

  Lean and Isabelle agree on n as the outer bound in both sums and on
  positive m and n. The Rocq source instead has m as the left outer bound
  and tautological nonnegativity assumptions; these are transcription
  inconsistencies with the stated problem, so the assertion below records
  the mutually agreeing canonical formulation.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a i j m n $.

  putnambench-putnam-1978-b6 $a |-
    A. a e. ( ( RR ^m NN0 ) ^m NN0 )
    A. m e. NN
    A. n e. NN
      (
        A. i e. NN0
          A. j e. NN0
            ( ( a ` i ) ` j ) e. ( 0 [,] 1 )
        ->
        (
          (
            sum_ i e. ( 1 ... n )
              sum_ j e. ( 1 ... ( m x. i ) )
                ( ( ( a ` i ) ` j ) / i )
          )
          ^
          2
        )
        <_
        (
          ( 2 x. m )
          x.
          (
            sum_ i e. ( 1 ... n )
              sum_ j e. ( 1 ... ( m x. i ) )
                ( ( a ` i ) ` j )
          )
        )
      )
  $.
$}
