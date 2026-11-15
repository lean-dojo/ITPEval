$(
  Statement-only formalization of PutnamBench artifact putnam_1965_b6:
  four real-plane points whose two pencils of circles always intersect are
  collinear or lie on one circle. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P65B6R2 is the real coordinate plane, P65B6Dist is Euclidean distance,
  and P65B6OnCircle O r X says that X lies on the circle with center O and
  radius r. P65B6Col4 requires every three of the four points to have zero
  determinant, which is equivalent to collinearity of their set even when
  some points coincide.

  Positive radii express the nondegenerate circles of the Isabelle and Rocq
  sources. In the Lean source the four points are distinct, so the radii of
  circles through A,B and through C,D are automatically positive. Conversely,
  if the four points are not distinct, their set has at most three points and
  is automatically either collinear or contained in a positive-radius circle.
  Thus omitting Lean's distinctness premise preserves the universally closed
  theorem while retaining the stronger degenerate cases stated by Isabelle.
  Every declaration below is an unproved $a statement, and this database
  contains no $p proof statement.
$)

$c P65B6I P65B6R2 P65B6Dist P65B6OnCircle P65B6Col P65B6Col4 $.

p65b6-index-syntax $a class P65B6I $.
p65b6-plane-syntax $a class P65B6R2 $.
p65b6-distance-syntax $a class ( P65B6Dist A B ) $.
p65b6-on-circle-syntax $a wff ( P65B6OnCircle O r A ) $.
p65b6-collinear-syntax $a wff ( P65B6Col A B C ) $.
p65b6-collinear-four-syntax $a wff ( P65B6Col4 A B C D ) $.

p65b6-index-definition $a |- P65B6I = ( 1 ... 2 ) $.

p65b6-plane-definition $a |- P65B6R2 = ( RR ^m P65B6I ) $.

${
  $d A B k $.

  p65b6-distance-definition $a |- (
    P65B6Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P65B6I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

p65b6-on-circle-definition $a |- (
  ( P65B6OnCircle O r A )
  <->
  ( P65B6Dist O A ) = r
) $.

p65b6-collinear-definition $a |- (
  ( P65B6Col A B C )
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

p65b6-collinear-four-definition $a |- (
  ( P65B6Col4 A B C D )
  <->
  (
    ( P65B6Col A B C )
    /\
    (
      ( P65B6Col A B D )
      /\
      (
        ( P65B6Col A C D )
        /\
        ( P65B6Col B C D )
      )
    )
  )
) $.

${
  $d A B C D I O P Q r s $.

  putnambench-putnam-1965-b6 $a |- (
    A. A e. P65B6R2
    A. B e. P65B6R2
    A. C e. P65B6R2
    A. D e. P65B6R2
      (
        (
          A. r e. RR
          A. s e. RR
          A. P e. P65B6R2
          A. Q e. P65B6R2
            (
              (
                (
                  0 < r
                  /\
                  0 < s
                )
                /\
                (
                  (
                    ( P65B6OnCircle P r A )
                    /\
                    ( P65B6OnCircle P r B )
                  )
                  /\
                  (
                    ( P65B6OnCircle Q s C )
                    /\
                    ( P65B6OnCircle Q s D )
                  )
                )
              )
              ->
              E. I e. P65B6R2
                (
                  ( P65B6OnCircle P r I )
                  /\
                  ( P65B6OnCircle Q s I )
                )
            )
        )
        ->
        (
          ( P65B6Col4 A B C D )
          \/
          E. r e. RR
          E. O e. P65B6R2
            (
              0 < r
              /\
              (
                ( P65B6OnCircle O r A )
                /\
                (
                  ( P65B6OnCircle O r B )
                  /\
                  (
                    ( P65B6OnCircle O r C )
                    /\
                    ( P65B6OnCircle O r D )
                  )
                )
              )
            )
        )
      )
  ) $.
$}
