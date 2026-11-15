$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_a1: positive integer sequences, coprime at every positive
  index and related by the stated rational recurrence, have only finitely
  many indices at which the shifted terms fail to be coprime. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 ^m NN0 is SetMM's class of all natural-valued sequences indexed by
  the nonnegative integers, and NN is the class of positive integers. Thus
  the first two universal conditions preserve positivity at every index and
  coprimality at every positive index. Complex division restricted to
  natural inputs is exact rational division, so the displayed recurrence is
  the source equality in QQ.

  For natural numbers, relative primality is equivalent to integer gcd equal
  to one. The restricted class in the conclusion is therefore exactly the
  source exceptional set, and membership in Fin states its finiteness. The
  declaration is the single unproved $a corpus statement; there is no $p
  proof declaration.
$)

${
  $d k m n $.

  putnambench-putnam-2025-a1 $a |-
    A. m e. ( NN0 ^m NN0 )
      A. n e. ( NN0 ^m NN0 )
        (
          (
            (
              A. k e. NN0
                (
                  0 < ( m ` k )
                  /\
                  0 < ( n ` k )
                )
              /\
              ( m ` 0 ) =/= ( n ` 0 )
            )
            /\
            (
              A. k e. NN
                ( ( m ` k ) gcd ( n ` k ) ) = 1
              /\
              A. k e. NN0
                (
                  ( ( m ` ( k + 1 ) ) / ( n ` ( k + 1 ) ) )
                  =
                  (
                    ( ( 2 x. ( m ` k ) ) + 1 )
                    /
                    ( ( 2 x. ( n ` k ) ) + 1 )
                  )
                )
            )
          )
          ->
          {
            k e. NN0
            |
            (
              (
                ( ( 2 x. ( m ` k ) ) + 1 )
                gcd
                ( ( 2 x. ( n ` k ) ) + 1 )
              )
              =/=
              1
            )
          }
          e.
          Fin
        )
  $.
$}
