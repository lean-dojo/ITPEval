$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_b1: the minimum number of distinct pairwise averages
  determined by an n-element set of real numbers is 2n - 3 for n at
  least 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The set-builder inlines the source definition of A_S. The first conjunct
  gives an internally existential n-element real set attaining cardinality
  2n - 3, and the second makes 2n - 3 a lower bound for the cardinality of
  the average set of every n-element real set. Together they are the explicit
  attained-minimum characterization of the source IsLeast/LEAST statement.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d S a b n x $.

  putnambench-putnam-1992-b1 $a |-
    A. n e. NN0
      (
        2 <_ n
        ->
        (
          E. S
            (
              (
                S C_ RR
                /\
                ( # ` S ) = n
              )
              /\
              (
                #
                `
                {
                  x e. RR |
                  E. a e. S E. b e. S
                    (
                      a =/= b
                      /\
                      ( ( a + b ) / 2 ) = x
                    )
                }
              )
              =
              ( ( 2 x. n ) - 3 )
            )
          /\
          A. S
            (
              (
                S C_ RR
                /\
                ( # ` S ) = n
              )
              ->
              ( ( 2 x. n ) - 3 )
              <_
              (
                #
                `
                {
                  x e. RR |
                  E. a e. S E. b e. S
                    (
                      a =/= b
                      /\
                      ( ( a + b ) / 2 ) = x
                    )
                }
              )
            )
        )
      )
  $.
$}
