$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_a5: two distinct real roots of the given cubic have
  unboundedly many common integer values in their floor-multiple sequences.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source parameters S and P are inlined by their defining formulas.
  Thus a and b range over the real roots of x^3 - 10x^2 + 29x - 25,
  while ( |_ ` ( c x. a ) ) and ( |_ ` ( d x. b ) ) are exactly the
  c-th and d-th terms of their floor sequences.

  The final restricted quantifiers say that above every nonnegative integer
  bound n there is an integer m attained by both sequences. This is the
  source's unbounded-common-values formulation of infinitely many positive
  integers appearing in both sequences.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c d m n $.

  putnambench-putnam-1979-a5 $a |-
    E. a e. RR
    E. b e. RR
      (
        a =/= b
        /\
        (
          (
            (
              ( a ^ 3 )
              -
              ( ; 1 0 x. ( a ^ 2 ) )
            )
            +
            ( ; 2 9 x. a )
          )
          -
          ; 2 5
        )
        =
        0
        /\
        (
          (
            (
              ( b ^ 3 )
              -
              ( ; 1 0 x. ( b ^ 2 ) )
            )
            +
            ( ; 2 9 x. b )
          )
          -
          ; 2 5
        )
        =
        0
        /\
        A. n e. NN0
          E. m e. ZZ
            (
              n < m
              /\
              E. c e. NN0
              E. d e. NN0
                (
                  ( |_ ` ( c x. a ) ) = m
                  /\
                  ( |_ ` ( d x. b ) ) = m
                )
            )
      )
  $.
$}
