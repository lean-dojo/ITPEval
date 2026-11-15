$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1982_a5: a strict lower bound for the positive gap between one and
  the sum of two positive-integer ratios whose numerators sum to at most
  1982. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Quantification over NN is exactly quantification over the positive integers,
  so it incorporates the four source positivity assumptions. Division and
  order are set.mm's standard exact number operations. The antecedent retains
  the bound on a + c and the strict ratio-sum inequality, and the conclusion
  reverses set.mm's less-than notation to state the source greater-than bound.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c d $.

  putnambench-putnam-1982-a5 $a |-
    A. a e. NN A. b e. NN A. c e. NN A. d e. NN
      (
        (
          ( a + c ) <_ ; ; ; 1 9 8 2
          /\
          ( ( a / b ) + ( c / d ) ) < 1
        )
        ->
        ( 1 / ( ; ; ; 1 9 8 3 ^ 3 ) )
        <
        ( ( 1 - ( a / b ) ) - ( c / d ) )
      )
  $.
$}
