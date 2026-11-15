$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_a2: the least possible Lebesgue area of a convex subset of
  the real plane meeting both branches of xy = 1 and both branches of
  xy = -1 is four. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P07A2R2 is the full real coordinate plane, with source coordinates 0 and 1
  relabeled as 1 and 2. P07A2Convex expands real convexity coordinatewise.
  P07A2Admissible keeps all four hyperbola-intersection points as internal
  existential witnesses, and P07A2Area is two-dimensional Lebesgue measure
  via set.mm's finite-dimensional volume function voln.

  The final conjunction is equivalent to saying that 4 is the least member
  of the set of areas of admissible sets: its first conjunct gives membership
  and its second gives the lower-bound property. All declarations are
  unproved $a statement encodings; this database contains no $p proof
  statement.
$)

$c P07A2I P07A2R2 P07A2Convex P07A2Admissible P07A2Area $.

p07a2-index-syntax $a class P07A2I $.
p07a2-plane-syntax $a class P07A2R2 $.
p07a2-convex-syntax $a wff ( P07A2Convex A ) $.
p07a2-admissible-syntax $a wff ( P07A2Admissible A ) $.
p07a2-area-syntax $a class ( P07A2Area A ) $.

p07a2-index-definition $a |- P07A2I = ( 1 ... 2 ) $.

p07a2-plane-definition $a |- P07A2R2 = ( RR ^m P07A2I ) $.

${
  $d A j t x y $.

  p07a2-convex-definition $a |- (
    ( P07A2Convex A )
    <->
    (
      A C_ P07A2R2
      /\
      A. x e. A A. y e. A A. t e. ( 0 [,] 1 )
        (
          j e. P07A2I |->
            (
              ( ( 1 - t ) x. ( x ` j ) )
              +
              ( t x. ( y ` j ) )
            )
        )
        e. A
    )
  ) $.
$}

${
  $d A p $.

  p07a2-admissible-definition $a |- (
    ( P07A2Admissible A )
    <->
    (
      ( P07A2Convex A )
      /\
      (
        E. p e. A
          (
            (
              0 < ( p ` 1 )
              /\
              0 < ( p ` 2 )
            )
            /\
            ( ( p ` 1 ) x. ( p ` 2 ) ) = 1
          )
        /\
        (
          E. p e. A
            (
              (
                ( p ` 1 ) < 0
                /\
                ( p ` 2 ) < 0
              )
              /\
              ( ( p ` 1 ) x. ( p ` 2 ) ) = 1
            )
          /\
          (
            E. p e. A
              (
                (
                  ( p ` 1 ) < 0
                  /\
                  0 < ( p ` 2 )
                )
                /\
                ( ( p ` 1 ) x. ( p ` 2 ) ) = ( -u 1 )
              )
            /\
            E. p e. A
              (
                (
                  0 < ( p ` 1 )
                  /\
                  ( p ` 2 ) < 0
                )
                /\
                ( ( p ` 1 ) x. ( p ` 2 ) ) = ( -u 1 )
              )
          )
        )
      )
    )
  ) $.
$}

p07a2-area-definition $a |- (
  P07A2Area A
) = (
  ( voln ` P07A2I )
  `
  A
) $.

${
  $d A S $.

  putnambench-putnam-2007-a2 $a |- (
    E. S e. ~P P07A2R2
      (
        ( P07A2Admissible S )
        /\
        ( P07A2Area S ) = 4
      )
    /\
    A. A e. ~P P07A2R2
      (
        ( P07A2Admissible A )
        ->
        4 <_ ( P07A2Area A )
      )
  ) $.
$}
