$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_b6: factorial-coin multiset counts satisfy matching
  exponential-power upper and lower bounds. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P07B6CoinWays(n) counts multiplicity functions on the distinct factorial
  values k! for 1 <= k <= n whose value-weighted sum is n!. Such functions
  are in bijection with the source multisets of coin values. Factorial is
  injective on positive indices, so there is one coordinate for each allowed
  coin value.

  For n >= 2 and real x, exp(x log n) is the source real power n^x. Thus the
  two displayed inequalities are exactly the requested bounds, with one real
  constant C independent of n. The auxiliary $a declarations below are
  syntax and a faithful definition, and the final $a is the single unproved
  corpus statement; this database contains no $p proof statement.
$)

$c P07B6CoinWays $.

p07b6-coin-ways-syntax $a class P07B6CoinWays $.

${
  $d g k m n $.

  p07b6-coin-ways-definition $a |- P07B6CoinWays =
    ( n e. NN0 |->
      (
        #
        `
        {
          g e.
          (
            NN0
            ^m
            {
              m e. NN |
              E. k e. ( 1 ... n )
                m = ( ! ` k )
            }
          ) |
          (
            sum_ m e.
              {
                m e. NN |
                E. k e. ( 1 ... n )
                  m = ( ! ` k )
              }
              (
                ( g ` m )
                x.
                m
              )
          )
          =
          ( ! ` n )
        }
      )
    )
  $.
$}

${
  $d C n $.

  putnambench-putnam-2007-b6 $a |-
    E. C e. RR
      A. n e. NN0
        (
          2 <_ n
          ->
          (
            (
              (
                exp
                `
                (
                  (
                    (
                      ( n ^ 2 )
                      /
                      2
                    )
                    -
                    ( C x. n )
                  )
                  x.
                  ( log ` n )
                )
              )
              x.
              (
                exp
                `
                (
                  ( -u ( n ^ 2 ) )
                  /
                  4
                )
              )
            )
            <_
            ( P07B6CoinWays ` n )
            /\
            ( P07B6CoinWays ` n )
            <_
            (
              (
                exp
                `
                (
                  (
                    (
                      ( n ^ 2 )
                      /
                      2
                    )
                    +
                    ( C x. n )
                  )
                  x.
                  ( log ` n )
                )
              )
              x.
              (
                exp
                `
                (
                  ( -u ( n ^ 2 ) )
                  /
                  4
                )
              )
            )
          )
        )
  $.
$}
