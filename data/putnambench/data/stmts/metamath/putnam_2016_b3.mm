$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_b3: every finite set of real-plane points whose three-point
  triangles have area at most 1 is contained in a triangle of area exactly 4.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P16B3I is the two-coordinate index set and P16B3R2 is the full real
  coordinate plane. P16B3Hull is exactly the convex hull of three points,
  expressed through internally existential nonnegative barycentric
  coordinates whose sum is one. P16B3Area is its planar Lebesgue measure
  through set.mm's finite-dimensional volume function voln.

  The final unproved $a assertion quantifies over every finite subset of the
  real plane. It preserves the universal area bound for all triples from the
  set and keeps the vertices of the containing area-4 triangle internally
  existentially quantified. This root candidate contains no $p proof
  declaration.
$)

$c P16B3I P16B3R2 P16B3Hull P16B3Area $.

p16b3-index-syntax $a class P16B3I $.
p16b3-plane-syntax $a class P16B3R2 $.
p16b3-hull-syntax $a class ( P16B3Hull A B C ) $.
p16b3-area-syntax $a class ( P16B3Area A B C ) $.

p16b3-index-definition $a |- P16B3I = ( 1 ... 2 ) $.

p16b3-plane-definition $a |- P16B3R2 = ( RR ^m P16B3I ) $.

${
  $d A B C i u v w z $.

  p16b3-hull-definition $a |- (
    P16B3Hull A B C
  ) = {
    z e. P16B3R2 |
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
          z =
            (
              i e. P16B3I |->
                (
                  (
                    ( u x. ( A ` i ) )
                    +
                    ( v x. ( B ` i ) )
                  )
                  +
                  ( w x. ( C ` i ) )
                )
            )
        )
      )
  } $.
$}

p16b3-area-definition $a |- (
  P16B3Area A B C
) = (
  ( voln ` P16B3I )
  `
  ( P16B3Hull A B C )
) $.

${
  $d A B C D E F S $.

  putnambench-putnam-2016-b3 $a |- A. S e. Fin
    (
      (
        S C_ P16B3R2
        /\
        A. A e. S A. B e. S A. C e. S
          ( P16B3Area A B C ) <_ 1
      )
      ->
      E. D e. P16B3R2
        E. E e. P16B3R2
          E. F e. P16B3R2
            (
              ( P16B3Area D E F ) = 4
              /\
              S C_ ( P16B3Hull D E F )
            )
    )
  $.
$}
