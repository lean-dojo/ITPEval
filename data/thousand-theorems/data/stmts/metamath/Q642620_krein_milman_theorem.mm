$(
  Statement-only formalization of Thousand Theorems corpus artifact Q642620
  (thousand-theorems__metamath__Q642620), "Krein&ndash;Milman theorem": every compact
  convex subset of an arbitrary Hausdorff locally convex real topological
  vector space is the closure of the convex hull of its extreme points. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q642620Convex W S is ordinary real convexity in the real vector space W.
  Q642620ConvexHull W S consists of all finite convex combinations of points
  of S; its finite carrier, coefficients, and points remain internally
  existentially quantified. Q642620ExtremePoints W S uses the equivalent
  characterization that a point of S lying in an open segment between two
  points of S forces both endpoints to equal that point.

  Q642620LocallyConvex W directly expands mathlib's neighborhood-basis
  characterization: every neighborhood of every point contains a convex
  neighborhood of that point. Neighborhood membership is expressed by
  containing an open set through the point.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q642620Convex Q642620ConvexHull Q642620ExtremePoints
   Q642620LocallyConvex $.

q642620-convex-syntax
  $a wff ( Q642620Convex W S ) $.
q642620-convex-hull-syntax
  $a class ( Q642620ConvexHull W S ) $.
q642620-extreme-points-syntax
  $a class ( Q642620ExtremePoints W S ) $.
q642620-locally-convex-syntax
  $a wff ( Q642620LocallyConvex W ) $.

${
  $d S W t x y $.

  q642620-convex-definition $a |- (
    ( Q642620Convex W S )
    <->
    A. x e. S A. y e. S A. t e. ( 0 [,] 1 )
      (
        (
          ( t ( .s ` W ) x )
          ( +g ` W )
          ( ( 1 - t ) ( .s ` W ) y )
        )
        e. S
      )
  ) $.
$}

${
  $d I S W c i p x $.

  q642620-convex-hull-definition $a |- (
    Q642620ConvexHull W S
  ) = {
    x e. ( Base ` W ) |
      E. I e. Fin
        E. c e. ( RR ^m I )
          E. p e. ( S ^m I )
            (
              A. i e. I
                ( 0g ` RRfld ) ( le ` RRfld ) ( c ` i )
              /\
              (
                (
                  RRfld gsum
                    ( i e. I |-> ( c ` i ) )
                )
                =
                ( 1r ` RRfld )
                /\
                x
                =
                (
                  W gsum
                    (
                      i e. I |->
                        (
                          ( c ` i )
                          ( .s ` W )
                          ( p ` i )
                        )
                    )
                )
              )
            )
  } $.
$}

${
  $d S W t x y z $.

  q642620-extreme-points-definition $a |- (
    Q642620ExtremePoints W S
  ) = {
    x e. S |
      A. y e. S A. z e. S
        (
          E. t e. ( 0 (,) 1 )
            x
            =
            (
              ( ( 1 - t ) ( .s ` W ) y )
              ( +g ` W )
              ( t ( .s ` W ) z )
            )
          ->
          ( y = x /\ z = x )
        )
  } $.
$}

${
  $d O P R U W x $.

  q642620-locally-convex-definition $a |- (
    ( Q642620LocallyConvex W )
    <->
    A. x e. ( Base ` W )
      A. U e. ~P ( Base ` W )
        (
          E. P e. ( TopOpen ` W )
            ( x e. P /\ P C_ U )
          ->
          E. O e. ~P ( Base ` W )
            (
              (
                E. R e. ( TopOpen ` W )
                  ( x e. R /\ R C_ O )
              )
              /\
              (
                ( Q642620Convex W O )
                /\
                O C_ U
              )
            )
        )
  ) $.
$}

${
  $d S W $.

  thousand-theorems-q642620-krein-milman $a |-
    A. W e. RRVec
      A. S e. ~P ( Base ` W )
        (
          (
            W e. TopMod
            /\
            ( TopOpen ` W ) e. Haus
            /\
            ( Q642620LocallyConvex W )
            /\
            ( ( TopOpen ` W ) |`t S ) e. Comp
            /\
            ( Q642620Convex W S )
          )
          ->
          (
            ( cls ` ( TopOpen ` W ) )
            `
            (
              Q642620ConvexHull
              W
              ( Q642620ExtremePoints W S )
            )
          )
          =
          S
        )
  $.
$}
