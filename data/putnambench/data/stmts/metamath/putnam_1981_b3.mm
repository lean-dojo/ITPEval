$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1981_b3: unboundedly many nonnegative integers n have the property
  that every prime divisor p of n^2 + 3 also divides k^2 + 3 for some
  nonnegative integer k with k^2 < n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers, Prime is its class of
  natural prime numbers, and || is integer divisibility. Restricting p to
  Prime is equivalent to the sources' implication guarded by primality.
  Natural and integer divisibility agree for the nonnegative expressions
  used here.

  The source predicate P is inlined at m. The existential witness k remains
  inside the universal quantifier over prime divisors, and the outer
  forall-exists statement says exactly that the satisfying integers are
  unbounded. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d k m n p $.

  putnambench-putnam-1981-b3 $a |-
    A. n e. NN0
      E. m e. NN0
        (
          n < m
          /\
          A. p e. Prime
            (
              p || ( ( m ^ 2 ) + 3 )
              ->
              E. k e. NN0
                (
                  ( k ^ 2 ) < m
                  /\
                  p || ( ( k ^ 2 ) + 3 )
                )
            )
        )
  $.
$}
