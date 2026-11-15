$(
  Statement-only formalization of PutnamBench artifact putnam_1962_a1:
  among five points in the real plane with no three collinear, some four
  are the vertices of a convex quadrilateral. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P62R2 is the real coordinate plane RR^2. P62Noncol is determinant
  noncollinearity, and P62NoncolSet says that every three distinct points
  of a set are noncollinear. P62Hull is the convex hull of a finite set,
  expressed by internally existential nonnegative barycentric weights.

  The final unproved $a assertion preserves the arbitrary five-point set,
  the quantification over all three-point subsets, and the internally
  existential four-point subset from the Lean and Isabelle sources.
$)

$c P62I P62R2 P62Noncol P62NoncolSet P62Hull $.

p62-index-syntax $a class P62I $.
p62-plane-syntax $a class P62R2 $.
p62-noncollinear-syntax $a wff ( P62Noncol A B C ) $.
p62-noncollinear-set-syntax $a wff ( P62NoncolSet A ) $.
p62-hull-syntax $a class ( P62Hull A ) $.

p62-index-definition $a |- P62I = ( 1 ... 2 ) $.

p62-plane-definition $a |- P62R2 = ( RR ^m P62I ) $.

p62-noncollinear-definition $a |- (
  ( P62Noncol A B C )
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
  $d A B C D $.

  p62-noncollinear-set-definition $a |- (
    ( P62NoncolSet A )
    <->
    (
      A C_ P62R2
      /\
      A. B e. A A. C e. A A. D e. A
        (
          (
            B =/= C
            /\
            (
              B =/= D
              /\
              C =/= D
            )
          )
          ->
          ( P62Noncol B C D )
        )
    )
  ) $.
$}

${
  $d A k w x z $.

  p62-hull-definition $a |- (
    P62Hull A
  ) = {
    z e. P62R2 |
    E. w
      (
        (
          w : A --> RR
          /\
          A. x e. A 0 <_ ( w ` x )
        )
        /\
        (
          ( sum_ x e. A ( w ` x ) ) = 1
          /\
          z =
            (
              k e. P62I |->
                sum_ x e. A
                  (
                    ( w ` x )
                    x.
                    ( x ` k )
                  )
            )
        )
      )
  } $.
$}

${
  $d A B C D S T s t $.

  putnambench-putnam-1962-a1 $a |- A. S
    (
      (
        (
          S C_ P62R2
          /\
          ( # ` S ) = 5
        )
        /\
        A. s e. { s e. ~P S | ( # ` s ) = 3 }
          ( P62NoncolSet s )
      )
      ->
      E. T
        (
          (
            T C_ S
            /\
            ( # ` T ) = 4
          )
          /\
          -. E. t e. T t e. ( P62Hull ( T \ { t } ) )
        )
    )
  $.
$}
