$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2011_b6: for every odd prime p, the factorial polynomial
  sum from k = 0 through p - 1 is nonzero modulo p for at least
  (p + 1) / 2 residue representatives. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime is set.mm's class of positive natural primes, and -. 2 || p
  states that p is odd. The interval ( 0 ..^ p ) is exactly the p-element
  set of residue representatives {0,...,p-1}. The restricted class in the
  conclusion contains precisely those n in this interval for which p does
  not divide sum_(k=0)^(p-1) k! n^k.

  Since p is odd, the real-arithmetic quotient ( p + 1 ) / 2 is the same
  natural number as the source's natural-number division. The hash operator
  gives the finite cardinality of the restricted residue set. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

${
  $d k n p $.

  putnambench-putnam-2011-b6 $a |- A. p e. Prime
    (
      -. 2 || p
      ->
      (
        ( ( p + 1 ) / 2 )
        <_
        (
          #
          `
          {
            n e. ( 0 ..^ p ) |
              -.
              p
              ||
              (
                sum_ k e. ( 0 ..^ p )
                  (
                    ( ! ` k )
                    x.
                    ( n ^ k )
                  )
              )
          }
        )
      )
    )
  $.
$}
