$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_a2: for a unit-circle arc in the open first quadrant, the
  sum of the areas below and to the left of the arc depends only on its
  angular length. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P98A2R2 is the real coordinate plane, P98A2Norm is its Euclidean norm,
  and P98A2Quadrant is the open-first-quadrant part of the unit circle.
  P98A2Arc P Q is the open arc selected by P_1 > R_1 > Q_1.
  P98A2AreaA and P98A2AreaB are the two-dimensional Lebesgue measures of
  the source regions, using set.mm's finite-dimensional volume function
  voln. P98A2Length is the positive first-quadrant angular difference.

  The source's quadrant, isarc, arc, A, and B parameters are eliminated by
  their displayed definitions. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

$c P98A2I P98A2R2 P98A2Norm P98A2Quadrant P98A2IsArc $.
$c P98A2Arc P98A2AreaA P98A2AreaB P98A2Length $.

p98a2-index-syntax $a class P98A2I $.
p98a2-plane-syntax $a class P98A2R2 $.
p98a2-norm-syntax $a class ( P98A2Norm P ) $.
p98a2-quadrant-syntax $a wff ( P98A2Quadrant P ) $.
p98a2-isarc-syntax $a wff ( P98A2IsArc P Q ) $.
p98a2-arc-syntax $a class ( P98A2Arc P Q ) $.
p98a2-area-a-syntax $a class ( P98A2AreaA P Q ) $.
p98a2-area-b-syntax $a class ( P98A2AreaB P Q ) $.
p98a2-length-syntax $a class ( P98A2Length P Q ) $.

p98a2-index-definition $a |- P98A2I = ( 1 ... 2 ) $.

p98a2-plane-definition $a |- P98A2R2 = ( RR ^m P98A2I ) $.

${
  $d P j $.

  p98a2-norm-definition $a |- (
    P98A2Norm P
  ) = (
    sqrt
    `
    (
      sum_ j e. P98A2I
        ( ( P ` j ) ^ 2 )
    )
  ) $.
$}

p98a2-quadrant-definition $a |- (
  ( P98A2Quadrant P )
  <->
  (
    P e. P98A2R2
    /\
    (
      (
        0 < ( P ` 1 )
        /\
        0 < ( P ` 2 )
      )
      /\
      ( P98A2Norm P ) = 1
    )
  )
) $.

p98a2-isarc-definition $a |- (
  ( P98A2IsArc P Q )
  <->
  (
    ( P98A2Quadrant P )
    /\
    (
      ( P98A2Quadrant Q )
      /\
      ( Q ` 1 ) < ( P ` 1 )
    )
  )
) $.

${
  $d P Q r $.

  p98a2-arc-definition $a |- (
    P98A2Arc P Q
  ) = {
    r e. P98A2R2 |
    (
      ( P98A2Quadrant r )
      /\
      (
        ( r ` 1 ) < ( P ` 1 )
        /\
        ( Q ` 1 ) < ( r ` 1 )
      )
    )
  } $.
$}

${
  $d P Q r s $.

  p98a2-area-a-definition $a |- (
    P98A2AreaA P Q
  ) = (
    ( voln ` P98A2I )
    `
    {
      s e. P98A2R2 |
      E. r e. ( P98A2Arc P Q )
        (
          ( r ` 1 ) = ( s ` 1 )
          /\
          (
            ( s ` 2 ) < ( r ` 2 )
            /\
            0 < ( s ` 2 )
          )
        )
    }
  ) $.
$}

${
  $d P Q r s $.

  p98a2-area-b-definition $a |- (
    P98A2AreaB P Q
  ) = (
    ( voln ` P98A2I )
    `
    {
      s e. P98A2R2 |
      E. r e. ( P98A2Arc P Q )
        (
          ( r ` 2 ) = ( s ` 2 )
          /\
          (
            ( s ` 1 ) < ( r ` 1 )
            /\
            0 < ( s ` 1 )
          )
        )
    }
  ) $.
$}

p98a2-length-definition $a |- (
  P98A2Length P Q
) = (
  (
    arctan
    `
    (
      ( Q ` 2 )
      /
      ( Q ` 1 )
    )
  )
  -
  (
    arctan
    `
    (
      ( P ` 2 )
      /
      ( P ` 1 )
    )
  )
) $.

${
  $d f p q $.

  putnambench-putnam-1998-a2 $a |-
    E. f e. ( RR ^m RR )
      A. p e. P98A2R2 A. q e. P98A2R2
        (
          ( P98A2IsArc p q )
          ->
          (
            (
              ( P98A2AreaA p q )
              +
              ( P98A2AreaB p q )
            )
            =
            ( f ` ( P98A2Length p q ) )
          )
        )
  $.
$}
