$(
  Statement-only formalization of "Morley's Theorem" from Hundred Theorems
  artifact 084: the intersections of adjacent internal angle trisectors of a
  noncollinear Euclidean triangle form an equilateral triangle. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  HT084R2 is the real Euclidean plane with coordinate index set HT084I.
  HT084Dist is ordinary Euclidean distance, and HT084Angle A B C is the total
  unoriented angle at B, with the same pi/2 convention for a zero ray as the
  HOL Light source. HT084Hull is the convex hull of three points through
  nonnegative barycentric coordinates, and HT084Noncol is planar
  noncollinearity via the two-dimensional determinant.

  The convex-hull hypotheses select the internal trisectors. The six angle
  equalities are the direct HOL Light and Isabelle formulation; they are
  equivalent to the positive angle-chain presentation in the Rocq source
  under the point correspondence (P,Q,T)_Rocq = (P,R,Q)_here. The conclusion
  states the two distance equalities making triangle R P Q equilateral. Every
  declaration below is an unproved $a statement.
$)

$c
  HT084I HT084R2 HT084Dist HT084Dot HT084Angle HT084Hull HT084Noncol
$.

ht084-index-syntax $a class HT084I $.
ht084-plane-syntax $a class HT084R2 $.
ht084-distance-syntax $a class ( HT084Dist A B ) $.
ht084-dot-syntax $a class ( HT084Dot A B C ) $.
ht084-angle-syntax $a class ( HT084Angle A B C ) $.
ht084-hull-syntax $a class ( HT084Hull A B C ) $.
ht084-noncollinear-syntax $a wff ( HT084Noncol A B C ) $.

ht084-index-definition $a |- HT084I = ( 1 ... 2 ) $.

ht084-plane-definition $a |- HT084R2 = ( RR ^m HT084I ) $.

${
  $d A B k $.

  ht084-distance-definition $a |- (
    HT084Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. HT084I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B C k $.

  ht084-dot-definition $a |- (
    HT084Dot A B C
  ) = (
    sum_ k e. HT084I
      (
        ( ( A ` k ) - ( B ` k ) )
        x.
        ( ( C ` k ) - ( B ` k ) )
      )
  ) $.
$}

ht084-angle-definition $a |- (
  HT084Angle A B C
) = if (
  (
    ( ( HT084Dist A B ) = 0 )
    \/
    ( ( HT084Dist C B ) = 0 )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      ( HT084Dot A B C )
      /
      (
        ( HT084Dist A B )
        x.
        ( HT084Dist C B )
      )
    )
  )
) $.

${
  $d A B C k u v w x $.

  ht084-hull-definition $a |- (
    HT084Hull A B C
  ) = {
    x e. HT084R2 |
    E. u e. RR E. v e. RR E. w e. RR
      (
        (
          0 <_ u
          /\
          (
            0 <_ v
            /\
            0 <_ w
          )
        )
        /\
        (
          ( ( u + v ) + w ) = 1
          /\
          x =
            (
              k e. HT084I |->
                (
                  (
                    ( u x. ( A ` k ) )
                    +
                    ( v x. ( B ` k ) )
                  )
                  +
                  ( w x. ( C ` k ) )
                )
            )
        )
      )
  } $.
$}

ht084-noncollinear-definition $a |- (
  ( HT084Noncol A B C )
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

${
  $d A B C P Q R $.

  hundred-theorems-084-morley $a |- (
    A. A e. HT084R2
    A. B e. HT084R2
    A. C e. HT084R2
    A. P e. HT084R2
    A. Q e. HT084R2
    A. R e. HT084R2
      (
        (
          (
            ( HT084Noncol A B C )
            /\
            (
              P e. ( HT084Hull A B C )
              /\
              (
                Q e. ( HT084Hull A B C )
                /\
                R e. ( HT084Hull A B C )
              )
            )
          )
          /\
          (
            ( ( HT084Angle A B R ) = ( ( HT084Angle A B C ) / 3 ) )
            /\
            (
              ( ( HT084Angle B A R ) = ( ( HT084Angle B A C ) / 3 ) )
              /\
              (
                ( ( HT084Angle B C P ) = ( ( HT084Angle B C A ) / 3 ) )
                /\
                (
                  ( ( HT084Angle C B P ) = ( ( HT084Angle C B A ) / 3 ) )
                  /\
                  (
                    ( ( HT084Angle C A Q ) = ( ( HT084Angle C A B ) / 3 ) )
                    /\
                    ( ( HT084Angle A C Q ) = ( ( HT084Angle A C B ) / 3 ) )
                  )
                )
              )
            )
          )
        )
        ->
        (
          ( ( HT084Dist R P ) = ( HT084Dist P Q ) )
          /\
          ( ( HT084Dist Q R ) = ( HT084Dist P Q ) )
        )
      )
  ) $.
$}
