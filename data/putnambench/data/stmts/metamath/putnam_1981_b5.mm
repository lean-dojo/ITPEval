$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1981_b5: the exponential of the infinite series whose nth term is
  the number of ones in the binary expansion of n divided by n(n+1) is
  rational. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P81B5B(n) counts exactly those nonnegative bit positions k for which
  floor(n / 2^k) is odd. For positive n this is the number of ones in its
  base-two expansion, matching the definitions in all ground-truth sources.

  SetMM's NN is the class of positive integers, and its unbounded sum_ binder
  is the real-series sum used by the sources. Membership of the exponential
  in QQ is equivalent to their existential rational-equality formulation.
  Since the specified solution proposition is True, the source biconditional
  reduces to this rationality assertion. All declarations are unproved $a
  statement encodings; this database contains no $p proof declaration.
$)

$c P81B5B $.

p81b5-b-syntax $a class P81B5B $.

${
  $d k n $.

  p81b5-b-definition $a |- P81B5B =
    ( n e. NN |->
      ( # `
        {
          k e. NN0 |
          ( ( ( |_ ` ( n / ( 2 ^ k ) ) ) mod 2 ) = 1 )
        }
      )
    )
  $.
$}

putnambench-putnam-1981-b5 $a |-
  (
    exp
    `
    (
      sum_ n e. NN
        (
          ( P81B5B ` n )
          /
          ( n x. ( n + 1 ) )
        )
    )
  )
  e. QQ
$.
