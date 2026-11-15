$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_b1: uniqueness of an equilateral three-point subset of the
  cubic curve x^3 + 3xy + y^3 = 1, whose triangle has area
  3 * sqrt(3) / 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P06B1R2 is the real coordinate plane and P06B1Dist is Euclidean distance.
  P06B1Curve is the stated cubic curve. P06B1Equilateral requires exactly
  three points and one common distance between every two distinct points.
  P06B1Hull is the convex hull of a finite set through internally existential
  nonnegative barycentric weights, and P06B1Area is its planar Lebesgue
  measure through set.mm's finite-dimensional volume function voln.

  The final declaration preserves the unique existential set and the separate
  existential area assertion from the formal sources, while inlining their
  annotated solution value. It is an unproved $a statement. This root candidate
  file declares no $p statement; the included set.mm library contains proofs.
$)

$c P06B1I P06B1R2 P06B1Dist P06B1Curve $.
$c P06B1Equilateral P06B1Hull P06B1Area $.

p06b1-index-syntax $a class P06B1I $.
p06b1-plane-syntax $a class P06B1R2 $.
p06b1-distance-syntax $a class ( P06B1Dist A B ) $.
p06b1-curve-syntax $a class P06B1Curve $.
p06b1-equilateral-syntax $a wff ( P06B1Equilateral S ) $.
p06b1-hull-syntax $a class ( P06B1Hull S ) $.
p06b1-area-syntax $a class ( P06B1Area S ) $.

p06b1-index-definition $a |- P06B1I = ( 1 ... 2 ) $.

p06b1-plane-definition $a |- P06B1R2 = ( RR ^m P06B1I ) $.

${
  $d A B k $.

  p06b1-distance-definition $a |- (
    P06B1Dist A B
  ) = (
    sqrt
    `
    (
      sum_ k e. P06B1I
        ( ( ( A ` k ) - ( B ` k ) ) ^ 2 )
    )
  ) $.
$}

p06b1-curve-definition $a |- P06B1Curve = {
  p e. P06B1R2 |
  (
    (
      (
        ( p ` 1 ) ^ 3
      )
      +
      (
        ( 3 x. ( p ` 1 ) )
        x.
        ( p ` 2 )
      )
    )
    +
    ( ( p ` 2 ) ^ 3 )
  )
  =
  1
} $.

${
  $d P Q S d $.

  p06b1-equilateral-definition $a |- (
    ( P06B1Equilateral S )
    <->
    (
      ( # ` S ) = 3
      /\
      E. d e. RR
        A. P e. S A. Q e. S
          (
            P =/= Q
            ->
            ( P06B1Dist P Q ) = d
          )
    )
  ) $.
$}

${
  $d S i w x z $.

  p06b1-hull-definition $a |- (
    P06B1Hull S
  ) = {
    z e. P06B1R2 |
    E. w
      (
        (
          w : S --> RR
          /\
          A. x e. S 0 <_ ( w ` x )
        )
        /\
        (
          ( sum_ x e. S ( w ` x ) ) = 1
          /\
          z =
            (
              i e. P06B1I |->
                sum_ x e. S
                  (
                    ( w ` x )
                    x.
                    ( x ` i )
                  )
            )
        )
      )
  } $.
$}

p06b1-area-definition $a |- (
  P06B1Area S
) = (
  ( voln ` P06B1I )
  `
  ( P06B1Hull S )
) $.

putnambench-putnam-2006-b1 $a |- (
  E! S e. ~P P06B1R2
    (
      S C_ P06B1Curve
      /\
      ( P06B1Equilateral S )
    )
  /\
  E. S e. ~P P06B1R2
    (
      (
        S C_ P06B1Curve
        /\
        ( P06B1Equilateral S )
      )
      /\
      ( P06B1Area S )
      =
      ( ( 3 x. ( sqrt ` 3 ) ) / 2 )
    )
) $.
