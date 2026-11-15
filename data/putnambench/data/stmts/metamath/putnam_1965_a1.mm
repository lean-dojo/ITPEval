$(
  Statement-only formalization of PutnamBench artifact putnam_1965_a1:
  a noncollinear real-plane triangle with ordered angles and two external
  angle-bisector points satisfying the stated equal-distance conditions has
  its angle at A equal to pi/15. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P65A1R2 is the real coordinate plane. P65A1Dist is Euclidean distance,
  P65A1Dot A B C is the inner product of the rays from B to A and C,
  P65A1Angle A B C is the total unoriented angle at B, and P65A1Col is
  determinant collinearity. The zero-ray branch of P65A1Angle is pi/2;
  otherwise it is arccos of the inner product divided by the product of the
  ray norms, exactly as in the Lean and Isabelle sources.

  The conclusion uses the published answer pi/15. Every declaration below is
  an unproved $a statement, and this database contains no $p proof statement.
$)

$c
  P65A1I P65A1R2 P65A1Dist P65A1Dot P65A1Angle P65A1Col
$.

p65a1-index-syntax $a class P65A1I $.
p65a1-plane-syntax $a class P65A1R2 $.
p65a1-distance-syntax $a class ( P65A1Dist A B ) $.
p65a1-dot-syntax $a class ( P65A1Dot A B C ) $.
p65a1-angle-syntax $a class ( P65A1Angle A B C ) $.
p65a1-collinear-syntax $a wff ( P65A1Col A B C ) $.

p65a1-index-definition $a |- P65A1I = ( 1 ... 2 ) $.

p65a1-plane-definition $a |- P65A1R2 = ( RR ^m P65A1I ) $.

${
  $d A B k $.

  p65a1-distance-definition $a |- (
    P65A1Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P65A1I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

${
  $d A B C k $.

  p65a1-dot-definition $a |- (
    P65A1Dot A B C
  ) = (
    sum_ k e. P65A1I
      (
        ( ( A ` k ) - ( B ` k ) )
        x.
        ( ( C ` k ) - ( B ` k ) )
      )
  ) $.
$}

p65a1-angle-definition $a |- (
  P65A1Angle A B C
) = if (
  (
    ( ( P65A1Dist A B ) = 0 )
    \/
    ( ( P65A1Dist C B ) = 0 )
  )
  ,
  ( _pi / 2 )
  ,
  (
    arccos
    `
    (
      ( P65A1Dot A B C )
      /
      (
        ( P65A1Dist A B )
        x.
        ( P65A1Dist C B )
      )
    )
  )
) $.

p65a1-collinear-definition $a |- (
  ( P65A1Col A B C )
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
  $d A B C X Y $.

  putnambench-putnam-1965-a1 $a |- (
    A. A e. P65A1R2
    A. B e. P65A1R2
    A. C e. P65A1R2
    A. X e. P65A1R2
    A. Y e. P65A1R2
      (
        (
          (
            -. ( P65A1Col A B C )
            /\
            (
              ( P65A1Angle C A B )
              <
              ( P65A1Angle B C A )
            )
          )
          /\
          (
            (
              ( P65A1Angle B C A )
              <
              ( _pi / 2 )
            )
            /\
            (
              ( _pi / 2 )
              <
              ( P65A1Angle A B C )
            )
          )
        )
        /\
        (
          (
            ( P65A1Col X B C )
            /\
            (
              ( P65A1Angle X A B )
              =
              (
                (
                  _pi
                  -
                  ( P65A1Angle C A B )
                )
                /
                2
              )
            )
          )
          /\
          (
            (
              ( P65A1Dist A X )
              =
              ( P65A1Dist A B )
            )
            /\
            (
              (
                ( P65A1Col Y C A )
                /\
                (
                  ( P65A1Angle Y B C )
                  =
                  (
                    (
                      _pi
                      -
                      ( P65A1Angle A B C )
                    )
                    /
                    2
                  )
                )
              )
              /\
              (
                ( P65A1Dist B Y )
                =
                ( P65A1Dist A B )
              )
            )
          )
        )
        ->
        (
          ( P65A1Angle C A B )
          =
          ( _pi / ; 1 5 )
        )
      )
  ) $.
$}
