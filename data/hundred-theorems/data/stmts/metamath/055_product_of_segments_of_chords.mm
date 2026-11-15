$(
  Statement-only formalization of "Product of Segments of Chords" from
  Hundred Theorems artifact 055: two chords through a common point, whose
  endpoints are equidistant from a center, have equal products of segment
  lengths. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  W ranges over arbitrary real inner-product spaces represented by set.mm
  CPreHil structures with scalar field RRfld. Points range over Base ` W.

  W HT055Between A B P is closed-segment betweenness: P is a convex affine
  combination of A and B with a real coefficient in the unit interval.
  W HT055Dist A B is the norm of B minus A. Thus both geometric notions are
  defined using the imported real scalar, vector, norm, and interval
  operations rather than left uninterpreted.

  The vector-space presentation is equivalent to the affine-space
  presentation after choosing an origin, and every expression below is
  invariant under that choice. The final declaration is the unproved corpus
  statement.
$)

$c HT055Between HT055Dist $.

ht055-between-syntax $a wff ( W HT055Between A B P ) $.
ht055-distance-syntax $a class ( W HT055Dist A B ) $.

${
  $d A B P W x $.

  ht055-between-definition $a |- (
    ( W HT055Between A B P )
    <->
    E. x e. ( 0 [,] 1 )
      P
      =
      (
        ( x ( .s ` W ) A )
        ( +g ` W )
        ( ( 1 - x ) ( .s ` W ) B )
      )
  ) $.
$}

ht055-distance-definition $a |- (
  W HT055Dist A B
) = (
  ( norm ` W ) ` ( B ( -g ` W ) A )
) $.

${
  $d A B C D O P R W $.

  hundred-theorems-055-product-of-segments-of-chords $a |- A. W
    (
      (
        W e. CPreHil
        /\
        ( Scalar ` W ) = RRfld
      )
      ->
      A. O e. ( Base ` W )
      A. R e. RR
      A. A e. ( Base ` W )
      A. B e. ( Base ` W )
      A. C e. ( Base ` W )
      A. D e. ( Base ` W )
      A. P e. ( Base ` W )
        (
          (
            (
              ( W HT055Between A B P )
              /\
              ( W HT055Between C D P )
            )
            /\
            (
              (
                ( W HT055Dist A O ) = R
                /\
                ( W HT055Dist B O ) = R
              )
              /\
              (
                ( W HT055Dist C O ) = R
                /\
                ( W HT055Dist D O ) = R
              )
            )
          )
          ->
          (
            (
              ( W HT055Dist A P )
              x.
              ( W HT055Dist P B )
            )
            =
            (
              ( W HT055Dist C P )
              x.
              ( W HT055Dist P D )
            )
          )
        )
    )
  $.
$}
