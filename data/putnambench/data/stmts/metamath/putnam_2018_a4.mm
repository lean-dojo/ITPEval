$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_a4: Beatty-step exponents in an arbitrary group force two
  elements to commute when the associated ordered product is the identity.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, m and n range over the positive integers NN, gcd is integer
  greatest common divisor, and |_ is the real floor function. The map A is
  a total integer-valued sequence on NN0; its values on 1 ... n are exactly
  the source exponents.

  G e. Grp supplies an arbitrary group, Base ` G is its carrier, +g ` G is
  its operation, 0g ` G is its identity, and .g ` G is integer group
  exponentiation. The map indexed by 1 ... n lists the factors
  g h^(A(k)) in increasing index order. SetMM's G gsum over a consecutive
  integer interval is their left-to-right group product, matching the
  source product.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d A G g h k m n $.

  putnambench-putnam-2018-a4 $a |-
    A. m e. NN A. n e. NN
      A. A e. ( ZZ ^m NN0 )
        A. G
          A. g e. ( Base ` G ) A. h e. ( Base ` G )
            (
              (
                (
                  ( m gcd n ) = 1
                  /\
                  A. k e. ( 1 ... n )
                    ( A ` k )
                    =
                    (
                      ( |_ ` ( ( m x. k ) / n ) )
                      -
                      ( |_ ` ( ( m x. ( k - 1 ) ) / n ) )
                    )
                )
                /\
                (
                  G e. Grp
                  /\
                  (
                    G
                    gsum
                    (
                      k e. ( 1 ... n ) |->
                        (
                          g
                          ( +g ` G )
                          (
                            ( A ` k )
                            ( .g ` G )
                            h
                          )
                        )
                    )
                  )
                  =
                  ( 0g ` G )
                )
              )
              ->
              (
                g ( +g ` G ) h
              )
              =
              (
                h ( +g ` G ) g
              )
            )
  $.
$}
