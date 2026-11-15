$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_b3: counting constant shifts of an irreducible monic quadratic
  that remain irreducible over an odd finite field. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  f is an arbitrary field structure with finite carrier of cardinality n.
  Poly1 ` f is SetMM's univariate polynomial ring over f; var1 is its
  variable, algSc embeds field elements as constant polynomials, and Irred
  is the set of irreducible ring elements. The equality defining p is the
  source polynomial x^2 + b x + c, while the set in the conclusion consists
  exactly of those d in f for which p + d is irreducible.

  Since n is odd, ( n - 1 ) / 2 is the integer-valued solution recorded in
  the ground-truth sources. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d b c d f n p $.

  putnambench-putnam-1979-b3 $a |-
    A. f
      A. n e. NN0
        A. b e. ( Base ` f )
          A. c e. ( Base ` f )
            A. p e. ( Base ` ( Poly1 ` f ) )
              (
                (
                  (
                    f e. Field
                    /\
                    (
                      ( Base ` f ) e. Fin
                      /\
                      ( # ` ( Base ` f ) ) = n
                    )
                  )
                  /\
                  -. 2 || n
                )
                /\
                (
                  p
                  =
                  (
                    (
                      2
                      ( .g ` ( mulGrp ` ( Poly1 ` f ) ) )
                      ( var1 ` f )
                    )
                    ( +g ` ( Poly1 ` f ) )
                    (
                      ( ( algSc ` ( Poly1 ` f ) ) ` b )
                      ( .r ` ( Poly1 ` f ) )
                      ( var1 ` f )
                    )
                  )
                  ( +g ` ( Poly1 ` f ) )
                  ( ( algSc ` ( Poly1 ` f ) ) ` c )
                )
                /\
                p e. ( Irred ` ( Poly1 ` f ) )
              )
              ->
              (
                #
                `
                {
                  d e. ( Base ` f ) |
                    (
                      p
                      ( +g ` ( Poly1 ` f ) )
                      ( ( algSc ` ( Poly1 ` f ) ) ` d )
                    )
                    e.
                    ( Irred ` ( Poly1 ` f ) )
                }
              )
              =
              ( ( n - 1 ) / 2 )
  $.
$}
