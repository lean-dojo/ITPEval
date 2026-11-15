$(
  Statement-only formalization of PutnamBench artifact putnam_1963_a6:
  the midpoint theorem for three distinct chords of a real-plane ellipse,
  with the intersections of the opposite-endpoint lines lying on the first
  chord's line. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P63A6R2 is the two-dimensional real coordinate plane. P63A6Dist is
  Euclidean distance, P63A6Mid is coordinatewise midpoint, P63A6Segment is
  the closed affine segment, and P63A6Col is determinant collinearity.
  P63A6Ellipse is the focus-and-distance-sum definition of the source set E.

  The Q, B, D collinearity premise follows the Lean statement and the
  mathematical problem description; the occurrence of P in that position
  in the Isabelle source is a typographical inconsistency. The explicit
  A =/= C and B =/= D line nondegeneracy premises are retained from Lean.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

$c
  P63A6I P63A6R2 P63A6Dist P63A6Mid P63A6Segment P63A6Col P63A6Ellipse
$.

p63a6-index-syntax $a class P63A6I $.
p63a6-plane-syntax $a class P63A6R2 $.
p63a6-distance-syntax $a class ( P63A6Dist A B ) $.
p63a6-midpoint-syntax $a class ( P63A6Mid A B ) $.
p63a6-segment-syntax $a class ( P63A6Segment A B ) $.
p63a6-collinear-syntax $a wff ( P63A6Col A B C ) $.
p63a6-ellipse-syntax $a class ( P63A6Ellipse F G r ) $.

p63a6-index-definition $a |- P63A6I = ( 1 ... 2 ) $.

p63a6-plane-definition $a |- P63A6R2 = ( RR ^m P63A6I ) $.

${
  $d A B j $.

  p63a6-distance-definition $a |- (
    P63A6Dist A B
  ) = (
    sqrt
    `
    (
      sum_ j e. P63A6I
        ( ( ( A ` j ) - ( B ` j ) ) ^ 2 )
    )
  ) $.

  p63a6-midpoint-definition $a |- (
    P63A6Mid A B
  ) = (
    j e. P63A6I |->
      (
        ( ( A ` j ) + ( B ` j ) )
        /
        2
      )
  ) $.
$}

${
  $d A B j t z $.

  p63a6-segment-definition $a |- (
    P63A6Segment A B
  ) = {
    z e. P63A6R2 |
    E. t e. ( 0 [,] 1 )
      z =
        (
          j e. P63A6I |->
            (
              ( ( 1 - t ) x. ( A ` j ) )
              +
              ( t x. ( B ` j ) )
            )
        )
  } $.
$}

p63a6-collinear-definition $a |- (
  ( P63A6Col A B C )
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
  $d F G H r $.

  p63a6-ellipse-definition $a |- (
    P63A6Ellipse F G r
  ) = {
    H e. P63A6R2 |
      (
        ( P63A6Dist F H )
        +
        ( P63A6Dist G H )
      )
      =
      r
  } $.
$}

${
  $d A B C D E F G M P Q U V r $.

  putnambench-putnam-1963-a6 $a |- (
    A. F e. P63A6R2
    A. G e. P63A6R2
    A. U e. P63A6R2
    A. V e. P63A6R2
    A. A e. P63A6R2
    A. B e. P63A6R2
    A. C e. P63A6R2
    A. D e. P63A6R2
    A. P e. P63A6R2
    A. Q e. P63A6R2
    A. r e. RR
    A. E
    A. M e. P63A6R2
      (
        (
          E = ( P63A6Ellipse F G r )
          /\
          (
            M = ( P63A6Mid U V )
            /\
            (
              ( P63A6Dist F G ) < r
              /\
              (
                (
                  U e. E
                  /\
                  (
                    V e. E
                    /\
                    U =/= V
                  )
                )
                /\
                (
                  (
                    A e. E
                    /\
                    (
                      B e. E
                      /\
                      A =/= B
                    )
                  )
                  /\
                  (
                    (
                      C e. E
                      /\
                      (
                        D e. E
                        /\
                        C =/= D
                      )
                    )
                    /\
                    (
                      A =/= C
                      /\
                      (
                        B =/= D
                        /\
                        (
                          (
                            ( P63A6Segment A B )
                            =/=
                            ( P63A6Segment U V )
                          )
                          /\
                          (
                            (
                              ( P63A6Segment C D )
                              =/=
                              ( P63A6Segment U V )
                            )
                            /\
                            (
                              (
                                ( P63A6Segment A B )
                                =/=
                                ( P63A6Segment C D )
                              )
                              /\
                              (
                                (
                                  M e. ( P63A6Segment A B )
                                  /\
                                  M e. ( P63A6Segment C D )
                                )
                                /\
                                (
                                  (
                                    ( P63A6Col P A C )
                                    /\
                                    ( P63A6Col P U V )
                                  )
                                  /\
                                  (
                                    ( P63A6Col Q B D )
                                    /\
                                    ( P63A6Col Q U V )
                                  )
                                )
                              )
                            )
                          )
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
        M = ( P63A6Mid P Q )
      )
  ) $.
$}
