$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1979_a4: equally many red and blue points in the real plane, with
  no three collinear, admit a perfect red-blue matching whose closed line
  segments are pairwise disjoint. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P79A4R2 is the real coordinate plane. P79A4Noncol is determinant
  noncollinearity, and P79A4Seg L t is the point with affine parameter t on
  the directed line through the endpoints of L.

  P79A4Data R B expands the source hypotheses: R and B are finite subsets of
  the plane, have equal cardinality, are disjoint, and every three distinct
  points in their union are noncollinear. P79A4Matching R B V says that V is
  a finite set of red-blue pairs, has the required cardinality, uses every
  endpoint at most once, and that any two distinct closed segments have no
  common point.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c
  P79A4R2 P79A4X P79A4Y P79A4Noncol P79A4Seg
  P79A4Data P79A4Matching
$.

p79a4-plane-syntax $a class P79A4R2 $.
p79a4-x-syntax $a class ( P79A4X A ) $.
p79a4-y-syntax $a class ( P79A4Y A ) $.
p79a4-noncollinear-syntax $a wff ( P79A4Noncol A B C ) $.
p79a4-segment-point-syntax $a class ( P79A4Seg A B ) $.
p79a4-data-syntax $a wff ( P79A4Data A B ) $.
p79a4-matching-syntax $a wff ( P79A4Matching A B C ) $.

p79a4-plane-definition $a |- P79A4R2 = ( RR X. RR ) $.

p79a4-x-definition $a |- ( P79A4X A ) = ( 1st ` A ) $.

p79a4-y-definition $a |- ( P79A4Y A ) = ( 2nd ` A ) $.

p79a4-noncollinear-definition $a |- (
  ( P79A4Noncol A B C )
  <->
  (
    (
      ( ( P79A4X B ) - ( P79A4X A ) )
      x.
      ( ( P79A4Y C ) - ( P79A4Y A ) )
    )
    =/=
    (
      ( ( P79A4Y B ) - ( P79A4Y A ) )
      x.
      ( ( P79A4X C ) - ( P79A4X A ) )
    )
  )
) $.

p79a4-segment-point-definition $a |- (
  P79A4Seg A B
) = <.
  (
    ( B x. ( P79A4X ( 1st ` A ) ) )
    +
    ( ( 1 - B ) x. ( P79A4X ( 2nd ` A ) ) )
  )
  ,
  (
    ( B x. ( P79A4Y ( 1st ` A ) ) )
    +
    ( ( 1 - B ) x. ( P79A4Y ( 2nd ` A ) ) )
  )
>. $.

${
  $d B R p q r $.

  p79a4-data-definition $a |- (
    ( P79A4Data R B )
    <->
    (
      (
        R e. Fin
        /\
        R C_ P79A4R2
      )
      /\
      (
        (
          B e. Fin
          /\
          B C_ P79A4R2
        )
        /\
        (
          ( # ` R ) = ( # ` B )
          /\
          (
            ( R i^i B ) = (/)
            /\
            A. p e. ( R u. B )
            A. q e. ( R u. B )
            A. r e. ( R u. B )
              (
                (
                  p =/= q
                  /\
                  (
                    p =/= r
                    /\
                    q =/= r
                  )
                )
                ->
                ( P79A4Noncol p q r )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d B R V l m x y $.

  p79a4-matching-definition $a |- (
    ( P79A4Matching R B V )
    <->
    (
      V e. Fin
      /\
      (
        V C_ ( R X. B )
        /\
        (
          ( # ` V ) = ( # ` R )
          /\
          A. l e. V
          A. m e. V
            (
              l =/= m
              ->
              (
                ( 1st ` l ) =/= ( 1st ` m )
                /\
                (
                  ( 2nd ` l ) =/= ( 2nd ` m )
                  /\
                  A. x e. RR
                  A. y e. RR
                    (
                      (
                        (
                          0 <_ x
                          /\
                          x <_ 1
                        )
                        /\
                        (
                          0 <_ y
                          /\
                          y <_ 1
                        )
                      )
                      ->
                      ( P79A4Seg l x ) =/= ( P79A4Seg m y )
                    )
                )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d B R v $.

  putnambench-putnam-1979-a4 $a |-
    (
      ( P79A4Data R B )
      ->
      E. v ( P79A4Matching R B v )
    )
  $.
$}
