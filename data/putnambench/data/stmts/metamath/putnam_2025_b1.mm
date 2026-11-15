$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2025_b1 (putnambench__metamath__putnam_2025_b1): every red-green
  coloring of the real Euclidean plane that preserves color at the
  circumcenter of each monochromatic noncollinear triple is constant. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  P25B1R2 is the full real coordinate plane. P25B1DistSq is squared
  Euclidean distance, P25B1Noncol is determinant noncollinearity, and
  P25B1Circumcenter O A B C says that O is equidistant from A, B, and C.
  Under P25B1Noncol A B C, that equidistant point exists uniquely and is
  exactly the circumcenter of the corresponding ordered 2-simplex.

  Relabeling the two coordinates from Fin 2 to 1 ... 2 is an isometry, and
  the two-element ordinal 2o = {0,1} is a definitional encoding of Bool.
  The condition that all three vertex colors agree is written using two
  equalities. Thus the final declaration retains the arbitrary coloring,
  every noncollinear triple, its circumcenter, and the internally
  existential constant color. It is a single unproved $a corpus statement;
  this database contains no $p proof declaration.
$)

$c P25B1I P25B1R2 P25B1DistSq P25B1Noncol P25B1Circumcenter $.

p25b1-index-syntax $a class P25B1I $.
p25b1-plane-syntax $a class P25B1R2 $.
p25b1-distance-square-syntax $a class ( P25B1DistSq A B ) $.
p25b1-noncollinear-syntax $a wff ( P25B1Noncol A B C ) $.
p25b1-circumcenter-syntax $a wff ( P25B1Circumcenter O A B C ) $.

p25b1-index-definition $a |- P25B1I = ( 1 ... 2 ) $.

p25b1-plane-definition $a |- P25B1R2 = ( RR ^m P25B1I ) $.

${
  $d A B k $.

  p25b1-distance-square-definition $a |- (
    P25B1DistSq A B
  ) = (
    sum_ k e. P25B1I
      ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
  ) $.
$}

p25b1-noncollinear-definition $a |- (
  ( P25B1Noncol A B C )
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

p25b1-circumcenter-definition $a |- (
  ( P25B1Circumcenter O A B C )
  <->
  (
    ( P25B1DistSq O A ) = ( P25B1DistSq O B )
    /\
    ( P25B1DistSq O A ) = ( P25B1DistSq O C )
  )
) $.

${
  $d A B C O P c f $.

  putnambench-putnam-2025-b1 $a |-
    A. f e. ( 2o ^m P25B1R2 )
      (
        (
          A. A e. P25B1R2
          A. B e. P25B1R2
          A. C e. P25B1R2
          A. O e. P25B1R2
            (
              (
                ( P25B1Noncol A B C )
                /\
                ( P25B1Circumcenter O A B C )
              )
              ->
              (
                (
                  ( f ` A ) = ( f ` B )
                  /\
                  ( f ` A ) = ( f ` C )
                )
                ->
                ( f ` O ) = ( f ` A )
              )
            )
        )
        ->
        E. c e. 2o
          A. P e. P25B1R2
            ( f ` P ) = c
      )
  $.
$}
