$(
  Statement-only formalization of PutnamBench artifact putnam_1966_b5:
  every finite set of at least three points in the real plane, with no three
  collinear, is the vertex set of a simple closed polygon whose distinct
  edges meet only at their endpoints. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P66B5R2 is the real coordinate plane, P66B5Succ is cyclic successor on
  1 ... N, P66B5Segment is the closed affine segment, and P66B5Noncol is
  determinant noncollinearity.

  A bijection L from 1 ... (# ` S) onto S is equivalent to the source's
  unique cyclic enumeration. Reindexing the finite cyclic carrier from ZMod
  (# ` S), or from naturals below # ` S, by 1 ... (# ` S) preserves adjacency
  through P66B5Succ. The intersection condition includes adjacent edges and
  permits exactly the four endpoints listed in the source statements.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c P66B5I P66B5R2 P66B5Succ P66B5Segment P66B5Noncol $.

p66b5-index-syntax $a class P66B5I $.
p66b5-plane-syntax $a class P66B5R2 $.
p66b5-successor-syntax $a class ( P66B5Succ N ) $.
p66b5-segment-syntax $a class ( P66B5Segment A B ) $.
p66b5-noncollinear-syntax $a wff ( P66B5Noncol A B C ) $.

p66b5-index-definition $a |- P66B5I = ( 1 ... 2 ) $.

p66b5-plane-definition $a |- P66B5R2 = ( RR ^m P66B5I ) $.

${
  $d N i $.

  p66b5-successor-definition $a |- (
    P66B5Succ N
  ) = (
    i e. ( 1 ... N ) |->
      if (
        i = N ,
        1 ,
        ( i + 1 )
      )
  ) $.
$}

${
  $d A B j t z $.

  p66b5-segment-definition $a |- (
    P66B5Segment A B
  ) = {
    z e. P66B5R2 |
    E. t e. ( 0 [,] 1 )
      z =
        (
          j e. P66B5I |->
            (
              ( ( 1 - t ) x. ( A ` j ) )
              +
              ( t x. ( B ` j ) )
            )
        )
  } $.
$}

p66b5-noncollinear-definition $a |- (
  ( P66B5Noncol A B C )
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
  $d A B C I L S i j $.

  putnambench-putnam-1966-b5 $a |- A. S e. Fin
    (
      (
        (
          S C_ P66B5R2
          /\
          3 <_ ( # ` S )
        )
        /\
        A. A e. S A. B e. S A. C e. S
          (
            (
              A =/= B
              /\
              (
                A =/= C
                /\
                B =/= C
              )
            )
            ->
            ( P66B5Noncol A B C )
          )
      )
      ->
      E. L
        (
          L : ( 1 ... ( # ` S ) ) -1-1-onto-> S
          /\
          A. i e. ( 1 ... ( # ` S ) )
          A. j e. ( 1 ... ( # ` S ) )
            (
              i =/= j
              ->
              A. I e. P66B5R2
                (
                  (
                    I e.
                      (
                        P66B5Segment
                          ( L ` i )
                          ( L ` ( ( P66B5Succ ( # ` S ) ) ` i ) )
                      )
                    /\
                    I e.
                      (
                        P66B5Segment
                          ( L ` j )
                          ( L ` ( ( P66B5Succ ( # ` S ) ) ` j ) )
                      )
                  )
                  ->
                  (
                    I = ( L ` i )
                    \/
                    (
                      I = ( L ` ( ( P66B5Succ ( # ` S ) ) ` i ) )
                      \/
                      (
                        I = ( L ` j )
                        \/
                        I = ( L ` ( ( P66B5Succ ( # ` S ) ) ` j ) )
                      )
                    )
                  )
                )
            )
        )
    )
  $.
$}
