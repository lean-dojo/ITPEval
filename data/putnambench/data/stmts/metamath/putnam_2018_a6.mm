$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_a6: rationality of the ratio of the areas of two triangles
  determined by four plane points, no three of which are collinear, whose
  six squared pairwise distances are rational. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P18A6R2 is the real coordinate plane. P18A6DistSq is squared Euclidean
  distance, and P18A6Noncol is determinant noncollinearity. P18A6Area is
  one half of the absolute determinant, hence exactly the planar Lebesgue
  area of the convex hull of its three vertices.

  P18A6Pair includes both parts of the source PPprops predicate: distinctness
  and rationality of squared distance. The conclusion keeps the rational
  witness internally existential. Since the hypotheses make both triangles
  nondegenerate, the quotient of these determinant areas is exactly the
  quotient of the source Lebesgue areas. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

$c P18A6I P18A6R2 P18A6DistSq P18A6Noncol P18A6Area P18A6Pair $.

p18a6-index-syntax $a class P18A6I $.
p18a6-plane-syntax $a class P18A6R2 $.
p18a6-distance-square-syntax $a class ( P18A6DistSq A B ) $.
p18a6-noncollinear-syntax $a wff ( P18A6Noncol A B C ) $.
p18a6-area-syntax $a class ( P18A6Area A B C ) $.
p18a6-pair-syntax $a wff ( P18A6Pair A B ) $.

p18a6-index-definition $a |- P18A6I = ( 1 ... 2 ) $.

p18a6-plane-definition $a |- P18A6R2 = ( RR ^m P18A6I ) $.

${
  $d A B k $.

  p18a6-distance-square-definition $a |- (
    P18A6DistSq A B
  ) = (
    sum_ k e. P18A6I
      ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
  ) $.
$}

p18a6-noncollinear-definition $a |- (
  ( P18A6Noncol A B C )
  <->
  (
    (
      ( ( B ` 1 ) - ( A ` 1 ) )
      x.
      ( ( C ` 2 ) - ( A ` 2 ) )
    )
    =/=
    (
      ( ( B ` 2 ) - ( A ` 2 ) )
      x.
      ( ( C ` 1 ) - ( A ` 1 ) )
    )
  )
) $.

p18a6-area-definition $a |- (
  P18A6Area A B C
) = (
  ( 1 / 2 )
  x.
  (
    abs
    `
    (
      (
        ( ( B ` 1 ) - ( A ` 1 ) )
        x.
        ( ( C ` 2 ) - ( A ` 2 ) )
      )
      -
      (
        ( ( B ` 2 ) - ( A ` 2 ) )
        x.
        ( ( C ` 1 ) - ( A ` 1 ) )
      )
    )
  )
) $.

p18a6-pair-definition $a |- (
  ( P18A6Pair A B )
  <->
  (
    A =/= B
    /\
    ( P18A6DistSq A B ) e. QQ
  )
) $.

${
  $d a b c d q $.

  putnambench-putnam-2018-a6 $a |- (
    A. a e. P18A6R2
    A. b e. P18A6R2
    A. c e. P18A6R2
    A. d e. P18A6R2
      (
        (
          (
            ( P18A6Noncol a b c )
            /\
            (
              ( P18A6Noncol a b d )
              /\
              (
                ( P18A6Noncol a c d )
                /\
                ( P18A6Noncol b c d )
              )
            )
          )
          /\
          (
            ( P18A6Pair a b )
            /\
            (
              ( P18A6Pair a c )
              /\
              (
                ( P18A6Pair a d )
                /\
                (
                  ( P18A6Pair b c )
                  /\
                  (
                    ( P18A6Pair b d )
                    /\
                    ( P18A6Pair c d )
                  )
                )
              )
            )
          )
        )
        ->
        E. q e. QQ
          (
            ( P18A6Area a b c )
            /
            ( P18A6Area a b d )
          )
          =
          q
      )
  ) $.
$}
