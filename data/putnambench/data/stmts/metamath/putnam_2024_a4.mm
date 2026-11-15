$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_a4: the primes greater than five admitting an integer
  geometric-power sequence whose rearrangement has a fixed nonzero
  consecutive difference modulo the prime form exactly the singleton
  set containing seven. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Prime is set.mm's class of positive natural primes, ZZ is the class of
  integers, and || is integer divisibility. For p greater than five, the
  inclusive interval 0 ... (p - 5) indexes exactly the powers
  1, a, ..., a^(p-5).

  The internally existential e is a bijection of this interval, so its
  values give precisely a rearrangement of those powers. This is equivalent
  to the Lean total function with BijOn on the interval: restriction gives
  the displayed bijection, while any displayed finite bijection can be
  extended arbitrarily to a total function on the natural numbers. Every
  argument of e used below lies in the interval.

  The bounds on r and the divisibility condition retain the integer
  witnesses and every consecutive index from 1 through p - 5. The final
  biconditional is the pointwise form of equality with the annotated
  solution set {7}. The final declaration is a single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d a e n p r $.

  putnambench-putnam-2024-a4 $a |- A. p e. NN
    (
      (
        (
          p e. Prime
          /\
          5 < p
        )
        /\
        E. a e. ZZ
          E. r e. ZZ
            (
              (
                1 <_ r
                /\
                r <_ ( p - 1 )
              )
              /\
              E. e
                (
                  e
                  :
                  ( 0 ... ( p - 5 ) )
                  -1-1-onto->
                  ( 0 ... ( p - 5 ) )
                  /\
                  A. n e. ( 1 ... ( p - 5 ) )
                    p
                    ||
                    (
                      (
                        ( a ^ ( e ` n ) )
                        -
                        ( a ^ ( e ` ( n - 1 ) ) )
                      )
                      -
                      r
                    )
                )
            )
      )
      <->
      p = 7
    )
  $.
$}
