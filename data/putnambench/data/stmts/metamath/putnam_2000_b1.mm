$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_b1: integer coefficients make at least four sevenths of a
  finite family of integer triples have odd resulting linear combination,
  when every triple has an odd coordinate. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The finite interval ( 1 ... n ) is in bijection with Fin n, and the
  function spaces quantify arbitrary integer-valued coordinate families on
  that carrier. For an integer x, -. 2 || x is exactly the assertion that x
  is odd. The cardinality comparison uses the real quotient ( 4 x. n ) / 7,
  preserving the source threshold without natural-number floor division.

  All coefficient witnesses remain internally existentially quantified. The
  final declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d a b c j n r s t $.

  putnambench-putnam-2000-b1 $a |-
    A. n e. NN
      A. a e. ( ZZ ^m ( 1 ... n ) )
        A. b e. ( ZZ ^m ( 1 ... n ) )
          A. c e. ( ZZ ^m ( 1 ... n ) )
            (
              A. j e. ( 1 ... n )
                (
                  -. 2 || ( a ` j )
                  \/
                  (
                    -. 2 || ( b ` j )
                    \/
                    -. 2 || ( c ` j )
                  )
                )
              ->
              E. r e. ZZ E. s e. ZZ E. t e. ZZ
                (
                  ( ( 4 x. n ) / 7 )
                  <_
                  (
                    #
                    `
                    {
                      j e. ( 1 ... n ) |
                      -. 2 ||
                        (
                          (
                            ( r x. ( a ` j ) )
                            +
                            ( s x. ( b ` j ) )
                          )
                          +
                          ( t x. ( c ` j ) )
                        )
                    }
                  )
                )
            )
  $.
$}
