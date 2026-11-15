$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_b5: a strict quadratic-sum bound forces A below twice every
  pairwise product among n real numbers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is SetMM's class of positive integers, and the explicit 1 < n hypothesis
  matches the published n > 1 assumption. The finite function a has domain
  1 ... n. Both inequalities are strict, unlike the non-strict hypothesis in
  the Rocq source.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a i j n r $.

  putnambench-putnam-1977-b5 $a |-
    A. n e. NN
    A. a e. ( RR ^m ( 1 ... n ) )
    A. r e. RR
      (
        (
          1 < n
          /\
          (
            r
            +
            sum_ i e. ( 1 ... n )
              ( ( a ` i ) ^ 2 )
          )
          <
          (
            (
              sum_ i e. ( 1 ... n )
                ( a ` i )
            )
            ^
            2
          )
          /
          ( n - 1 )
        )
        ->
        A. i e. ( 1 ... n )
        A. j e. ( 1 ... n )
          (
            i < j
            ->
            r < ( 2 x. ( a ` i ) x. ( a ` j ) )
          )
      )
  $.
$}
