$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1984_a6: dependence of the last nonzero digit of a factorial at
  sums of distinct powers of five on the exponent sum, with least eventual
  period four. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is set.mm's class of nonnegative integers, NN is its class of positive
  integers, and ! is factorial. The antecedent characterizes f(n) as the last
  nonzero decimal digit of n!: after removing an internally existential power
  of ten, q is the remaining positive integer and q mod 10 is nonzero.

  The carrier 0 ..^ k has exactly k elements and represents Fin k. Requiring
  a to be one-to-one on that whole carrier is exactly the distinct-exponent
  condition. The first conclusion conjunct defines the induced function g on
  exponent sums. The remaining conjuncts say that 4 is a period of g from
  index 1 and is no larger than any positive period, so it is the least
  positive such period. The auxiliary predicates from the sources are thus
  inlined definitionally. The final declaration is a single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d a f g i k n p q s t $.

  putnambench-putnam-1984-a6 $a |-
    A. f e. ( NN0 ^m NN0 )
      (
        A. n e. NN0
          E. t e. NN0
            E. q e. NN
              (
                ( ! ` n )
                =
                ( ( ; 1 0 ^ t ) x. q )
                /\
                (
                  ( f ` n ) = ( q mod ; 1 0 )
                  /\
                  ( q mod ; 1 0 ) =/= 0
                )
              )
        ->
        E. g e. ( NN0 ^m NN0 )
          (
            A. k e. NN
              A. a e. ( NN0 ^m ( 0 ..^ k ) )
                (
                  a : ( 0 ..^ k ) -1-1-> NN0
                  ->
                  (
                    f
                    `
                    (
                      sum_ i e. ( 0 ..^ k )
                        ( 5 ^ ( a ` i ) )
                    )
                  )
                  =
                  (
                    g
                    `
                    (
                      sum_ i e. ( 0 ..^ k )
                        ( a ` i )
                    )
                  )
                )
            /\
            (
              A. s e. NN
                ( g ` s ) = ( g ` ( s + 4 ) )
              /\
              A. p e. NN
                (
                  A. s e. NN
                    ( g ` s ) = ( g ` ( s + p ) )
                  ->
                  4 <_ p
                )
            )
          )
      )
  $.
$}
