$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2019_b5: the unique positive Fibonacci indices whose difference
  equals the value at 2019 of the degree-1008 odd-node interpolation
  polynomial are 2019 and 1010. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all integer-valued sequences on NN0, and the recurrence over
  NN together with the two initial values is exactly the positive-indexed
  Fibonacci definition. P ranges over Set.mm's full class Poly ` RR of real
  polynomial functions; deg is exact degree and function application is
  polynomial evaluation. The interval 0 ... 1008 preserves all 1009 source
  interpolation nodes.

  The positivity conjuncts retain the Lean primary source's quantification
  over all natural j and k while excluding the unconstrained zeroth sequence
  value. Inlining the annotated solution pair makes its equality equivalent
  to j = 2019 and k = 1010. The declaration below is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d F P j k n $.

  putnambench-putnam-2019-b5 $a |-
    A. F e. ( ZZ ^m NN0 )
      A. P e. ( Poly ` RR )
        (
          (
            (
              A. n e. NN
                ( F ` ( n + 2 ) )
                =
                (
                  ( F ` ( n + 1 ) )
                  +
                  ( F ` n )
                )
              /\
              (
                ( F ` 1 ) = 1
                /\
                ( F ` 2 ) = 1
              )
            )
            /\
            (
              ( deg ` P ) = ( ; ; ; 1 0 0 8 )
              /\
              A. n e. ( 0 ... ( ; ; ; 1 0 0 8 ) )
                (
                  P
                  `
                  ( ( 2 x. n ) + 1 )
                )
                =
                (
                  F
                  `
                  ( ( 2 x. n ) + 1 )
                )
            )
          )
          ->
          A. j e. NN0
            A. k e. NN0
              (
                (
                  (
                    (
                      P
                      `
                      ( ; ; ; 2 0 1 9 )
                    )
                    =
                    (
                      ( F ` j )
                      -
                      ( F ` k )
                    )
                  )
                  /\
                  (
                    1 <_ j
                    /\
                    1 <_ k
                  )
                )
                <->
                (
                  j = ( ; ; ; 2 0 1 9 )
                  /\
                  k = ( ; ; ; 1 0 1 0 )
                )
              )
        )
  $.
$}
