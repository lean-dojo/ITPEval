$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1976_b6: every nonnegative integer whose positive divisors sum to
  twice the integer plus one is the square of an odd integer. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and ZZ are the standard nonnegative-integer and integer classes from
  set.mm. The expression ( 1 sigma N ) is the sum of the positive divisors
  of N, so the antecedent is exactly the quasiperfect-number definition from
  the source statements. Nondivisibility of m by 2 states that m is odd.

  Inlining the source definitions of sigma and quasiperfect is definitionally
  equivalent to their quantified formulations. The integer square witness
  remains internally existentially quantified. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d N m $.

  putnambench-putnam-1976-b6 $a |-
    A. N e. NN0
      (
        ( 1 sigma N ) = ( ( 2 x. N ) + 1 )
        ->
        E. m e. ZZ
          (
            -. 2 || m
            /\
            ( m ^ 2 ) = N
          )
      )
  $.
$}
