$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1981_a1: the greatest exponent E(n) for which 5^E(n) divides
  the integer product 1^1 2^2 ... n^n satisfies
  E(n) / n^2 tending to 1/8. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  E ranges over all nonnegative-integer-valued sequences. For every positive
  integer n, the antecedent says both that 5^(E(n)) divides the inclusive
  finite product and that every nonnegative exponent with this divisibility
  property is at most E(n). Thus it inlines the source predicate P and
  preserves the source greatest-exponent condition.

  The value E(0) is unconstrained, as in the Lean and Rocq sources, and does
  not affect the sequence limit. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d E k m n $.

  putnambench-putnam-1981-a1 $a |- A. E e. ( NN0 ^m NN0 )
    (
      (
        A. n e. NN
          (
            (
              ( 5 ^ ( E ` n ) )
              ||
              prod_ m e. ( 1 ... n ) ( m ^ m )
            )
            /\
            A. k e. NN0
              (
                (
                  ( 5 ^ k )
                  ||
                  prod_ m e. ( 1 ... n ) ( m ^ m )
                )
                ->
                k <_ ( E ` n )
              )
          )
      )
      ->
      (
        n e. NN0 |->
          (
            ( E ` n )
            /
            ( n ^ 2 )
          )
      )
      ~~>
      ( 1 / 8 )
    )
  $.
$}
