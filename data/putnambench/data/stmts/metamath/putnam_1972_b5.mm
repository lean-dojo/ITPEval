$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1972_b5: a noncoplanar quadrilateral in real three-space with two
  pairs of equal opposite angles has the corresponding pairs of opposite
  sides equal in length. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P72B5R3 is real coordinate three-space. P72B5Dist is ordinary Euclidean
  distance, and P72B5Angle A B C is the total unoriented angle at B, with
  value pi/2 when either ray is zero, exactly as in the Lean and Isabelle
  sources.

  P72B5Coplanar S says that there are two vectors u and v such that every
  difference x - y of members of S is a real linear combination of u and v.
  The coordinate equation used below is exactly x - y = c u + d v, rewritten
  as x = y + c u + d v. All spanning vectors and scalar coefficients remain
  internally existentially quantified.

  The final declaration universally quantifies all four points and is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

$c P72B5I P72B5R3 P72B5Dist P72B5Dot P72B5Angle P72B5Coplanar $.

p72b5-index-syntax $a class P72B5I $.
p72b5-space-syntax $a class P72B5R3 $.
p72b5-distance-syntax $a class ( P72B5Dist A B ) $.
p72b5-dot-syntax $a class ( P72B5Dot A B C ) $.
p72b5-angle-syntax $a class ( P72B5Angle A B C ) $.
p72b5-coplanar-syntax $a wff ( P72B5Coplanar S ) $.

p72b5-index-definition $a |- P72B5I = ( 1 ... 3 ) $.

p72b5-space-definition $a |- P72B5R3 = ( RR ^m P72B5I ) $.

${
  $d A B k $.

  p72b5-distance-definition $a |- (
    P72B5Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P72B5I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B C k $.

  p72b5-dot-definition $a |- (
    P72B5Dot A B C
  ) = (
    sum_ k e. P72B5I
      (
        ( ( A ` k ) - ( B ` k ) )
        x.
        ( ( C ` k ) - ( B ` k ) )
      )
  ) $.
$}

p72b5-angle-definition $a |- (
  P72B5Angle A B C
) = if (
  (
    ( ( P72B5Dist A B ) = 0 )
    \/
    ( ( P72B5Dist C B ) = 0 )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      ( P72B5Dot A B C )
      /
      (
        ( P72B5Dist A B )
        x.
        ( P72B5Dist C B )
      )
    )
  )
) $.

${
  $d S c d i u v x y $.

  p72b5-coplanar-definition $a |- (
    ( P72B5Coplanar S )
    <->
    (
      S C_ P72B5R3
      /\
      E. u e. P72B5R3 E. v e. P72B5R3
        A. x e. S A. y e. S
          E. c e. RR E. d e. RR
            x =
              (
                i e. P72B5I |->
                  (
                    ( y ` i )
                    +
                    (
                      ( c x. ( u ` i ) )
                      +
                      ( d x. ( v ` i ) )
                    )
                  )
              )
    )
  ) $.
$}

${
  $d A B C D $.

  putnambench-putnam-1972-b5 $a |-
    A. A e. P72B5R3
    A. B e. P72B5R3
    A. C e. P72B5R3
    A. D e. P72B5R3
      (
        (
          -.
            (
              P72B5Coplanar
                ( { A , B } u. { C , D } )
            )
          /\
          (
            ( P72B5Angle A B C ) = ( P72B5Angle C D A )
            /\
            ( P72B5Angle B C D ) = ( P72B5Angle D A B )
          )
        )
        ->
        (
          ( P72B5Dist A B ) = ( P72B5Dist C D )
          /\
          ( P72B5Dist B C ) = ( P72B5Dist D A )
        )
      )
  $.
$}
