$(
  Statement-only formalization of PutnamBench artifact putnam_1966_a2:
  the reciprocal-square inequality for the side lengths, semiperimeter, and
  inradius of a noncollinear real-plane triangle. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P66A2R2 is the real coordinate plane. P66A2Dist is Euclidean distance,
  P66A2Col is determinant collinearity, and P66A2Hull is the convex hull of
  three points via nonnegative barycentric coordinates. P66A2UniqueTangency
  states existence and uniqueness, within the plane, of a point on the line
  through its last two arguments at the specified distance from its first.

  The final unproved $a assertion preserves the arbitrary real parameters,
  noncollinearity assumption, internally existential incenter, three unique
  tangency conditions, closed-disk containment, and reciprocal-square
  conclusion of the Lean and Isabelle sources. This database has no $p proof
  statement.
$)

$c P66A2I P66A2R2 P66A2Dist P66A2Col P66A2Hull
   P66A2UniqueTangency $.

p66a2-index-syntax $a class P66A2I $.
p66a2-plane-syntax $a class P66A2R2 $.
p66a2-distance-syntax $a class ( P66A2Dist A B ) $.
p66a2-collinear-syntax $a wff ( P66A2Col A B C ) $.
p66a2-hull-syntax $a class ( P66A2Hull A B C ) $.
p66a2-unique-tangency-syntax $a
  wff ( P66A2UniqueTangency I r A B ) $.

p66a2-index-definition $a |- P66A2I = ( 1 ... 2 ) $.

p66a2-plane-definition $a |- P66A2R2 = ( RR ^m P66A2I ) $.

${
  $d A B j $.

  p66a2-distance-definition $a |- (
    P66A2Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P66A2I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.
$}

p66a2-collinear-definition $a |- (
  ( P66A2Col A B C )
  <->
  (
    (
      ( ( B ` 1 ) - ( A ` 1 ) )
      x.
      ( ( C ` 2 ) - ( A ` 2 ) )
    )
    =
    (
      ( ( B ` 2 ) - ( A ` 2 ) )
      x.
      ( ( C ` 1 ) - ( A ` 1 ) )
    )
  )
) $.

${
  $d A B C j u v w x $.

  p66a2-hull-definition $a |- (
    P66A2Hull A B C
  ) = {
    x e. P66A2R2 |
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
              j e. P66A2I |->
                (
                  (
                    ( u x. ( A ` j ) )
                    +
                    ( v x. ( B ` j ) )
                  )
                  +
                  ( w x. ( C ` j ) )
                )
            )
        )
      )
  } $.
$}

${
  $d A B I P Q r $.

  p66a2-unique-tangency-definition $a |- (
    ( P66A2UniqueTangency I r A B )
    <->
    E. P e. P66A2R2
      (
        (
          ( P66A2Dist I P ) = r
          /\
          ( P66A2Col P A B )
        )
        /\
        A. Q e. P66A2R2
          (
            (
              ( P66A2Dist I Q ) = r
              /\
              ( P66A2Col Q A B )
            )
            ->
            Q = P
          )
      )
  ) $.
$}

${
  $d A B C I Z a b c p r $.

  putnambench-putnam-1966-a2 $a |-
    A. r e. RR
    A. A e. P66A2R2
    A. B e. P66A2R2
    A. C e. P66A2R2
    A. a e. RR
    A. b e. RR
    A. c e. RR
    A. p e. RR
      (
        (
          -. ( P66A2Col A B C )
          /\
          (
            a = ( P66A2Dist B C )
            /\
            (
              b = ( P66A2Dist C A )
              /\
              (
                c = ( P66A2Dist A B )
                /\
                (
                  p =
                    (
                      (
                        (
                          ( P66A2Dist B C )
                          +
                          ( P66A2Dist C A )
                        )
                        +
                        ( P66A2Dist A B )
                      )
                      /
                      2
                    )
                  /\
                  E. I e. P66A2R2
                    (
                      ( P66A2UniqueTangency I r B C )
                      /\
                      (
                        ( P66A2UniqueTangency I r C A )
                        /\
                        (
                          ( P66A2UniqueTangency I r A B )
                          /\
                          A. Z e. P66A2R2
                            (
                              ( P66A2Dist I Z ) <_ r
                              ->
                              Z e. ( P66A2Hull A B C )
                            )
                        )
                      )
                    )
                )
              )
            )
          )
        )
        ->
        (
          ( 1 / ( r ^ 2 ) )
          <_
          (
            (
              ( 1 / ( ( p - a ) ^ 2 ) )
              +
              ( 1 / ( ( p - b ) ^ 2 ) )
            )
            +
            ( 1 / ( ( p - c ) ^ 2 ) )
          )
        )
      )
  $.
$}
