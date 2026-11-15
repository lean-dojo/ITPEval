$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1997_a4: an arbitrary group self-map whose triple products agree
  on all identity-product triples can be left-translated into a group
  homomorphism. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, g e. Grp supplies an arbitrary group, Base ` g is its carrier,
  +g ` g is its group operation, and 0g ` g is its identity. The function
  p ranges over every total self-map of the carrier.

  The six universally quantified elements and both identity-product
  conditions reproduce the source hypothesis. The element a remains
  existentially quantified inside the conclusion, where the displayed
  equation states directly that x |-> a (+g ` G) (P ` x) is a group
  homomorphism. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d a b c d e g h p x y z $.

  putnambench-putnam-1997-a4 $a |- A. g
    (
      g e. Grp
      ->
      A. p e. ( ( Base ` g ) ^m ( Base ` g ) )
        (
          A. a e. ( Base ` g )
            A. b e. ( Base ` g )
              A. c e. ( Base ` g )
                A. d e. ( Base ` g )
                  A. e e. ( Base ` g )
                    A. h e. ( Base ` g )
                      (
                        (
                          (
                            ( a ( +g ` g ) b )
                            ( +g ` g )
                            c
                          )
                          =
                          ( 0g ` g )
                          /\
                          (
                            ( d ( +g ` g ) e )
                            ( +g ` g )
                            h
                          )
                          =
                          ( 0g ` g )
                        )
                        ->
                        (
                          (
                            ( ( p ` a ) ( +g ` g ) ( p ` b ) )
                            ( +g ` g )
                            ( p ` c )
                          )
                          =
                          (
                            ( ( p ` d ) ( +g ` g ) ( p ` e ) )
                            ( +g ` g )
                            ( p ` h )
                          )
                        )
                      )
          ->
          E. z e. ( Base ` g )
            A. x e. ( Base ` g )
              A. y e. ( Base ` g )
                (
                  z
                  ( +g ` g )
                  (
                    p
                    `
                    ( x ( +g ` g ) y )
                  )
                )
                =
                (
                  ( z ( +g ` g ) ( p ` x ) )
                  ( +g ` g )
                  ( z ( +g ` g ) ( p ` y ) )
                )
        )
    )
  $.
$}
