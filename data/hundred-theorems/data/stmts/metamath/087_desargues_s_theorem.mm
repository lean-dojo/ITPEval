$(
  Statement-only formalization of "Desargues's Theorem" from Hundred
  Theorems artifact 087: the projective incidence theorem for two
  perspective triangles and its affine parallel-line specialization over
  the real plane. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  HT087PPlane is the real projective plane: its points are equivalence
  classes of nonzero triples of reals under multiplication by a nonzero real
  scalar. HT087PCol is projective collinearity, expressed by a zero
  determinant of representatives.

  HT087R2 is the real affine plane. HT087ACol is affine collinearity,
  HT087Triangle is noncollinearity, and HT087Parallel says that the direction
  vectors of two affine lines are linearly dependent.

  In the projective assertion D, E, and F denote the source points A', B',
  and C'. In the affine assertion they denote A1, B1, and C1. The first
  assertion preserves the HOL Light nondegeneracy and incidence hypotheses;
  the second preserves the Rocq inequalities, triangle hypotheses,
  perspectivity center, and parallel-side hypotheses. The supplied Isabelle
  source contains affine-space infrastructure but no Desargues proposition.
  Every declaration below is an unproved $a statement.
$)

$c
  HT087R2 HT087R3 HT087X HT087Y HT087PY HT087Z HT087Scale HT087HClass
  HT087PPlane HT087Det HT087PCol HT087ACol HT087Triangle HT087Parallel
  HT087PND HT087PConfig HT087AffineHyp
$.

ht087-r2-syntax $a class HT087R2 $.
ht087-r3-syntax $a class HT087R3 $.
ht087-x-syntax $a class ( HT087X A ) $.
ht087-y-syntax $a class ( HT087Y A ) $.
ht087-py-syntax $a class ( HT087PY A ) $.
ht087-z-syntax $a class ( HT087Z A ) $.
ht087-scale-syntax $a class ( HT087Scale A B ) $.
ht087-hclass-syntax $a class ( HT087HClass A ) $.
ht087-pplane-syntax $a class HT087PPlane $.
ht087-det-syntax $a class ( HT087Det A B C ) $.
ht087-pcol-syntax $a wff ( HT087PCol A B C ) $.
ht087-acol-syntax $a wff ( HT087ACol A B C ) $.
ht087-triangle-syntax $a wff ( HT087Triangle A B C ) $.
ht087-parallel-syntax $a wff ( HT087Parallel A B C D ) $.
ht087-pnd-syntax
  $a wff ( HT087PND A B C D E F P Q R S ) $.
ht087-pconfig-syntax
  $a wff ( HT087PConfig A B C D E F P Q R S ) $.
ht087-affine-hyp-syntax
  $a wff ( HT087AffineHyp A B C D E F S ) $.

ht087-r2-definition $a |- HT087R2 = ( RR X. RR ) $.

ht087-r3-definition $a |- HT087R3 = ( RR X. ( RR X. RR ) ) $.

ht087-x-definition $a |- ( HT087X A ) = ( 1st ` A ) $.

ht087-y-definition $a |- ( HT087Y A ) = ( 2nd ` A ) $.

ht087-py-definition $a |- ( HT087PY A ) = ( 1st ` ( 2nd ` A ) ) $.

ht087-z-definition $a |- ( HT087Z A ) = ( 2nd ` ( 2nd ` A ) ) $.

ht087-scale-definition $a |- ( HT087Scale A B ) =
  <.
    ( A x. ( HT087X B ) )
    ,
    <.
      ( A x. ( HT087PY B ) )
      ,
      ( A x. ( HT087Z B ) )
    >.
  >.
$.

${
  $d A B k $.

  ht087-hclass-definition $a |- ( HT087HClass A ) =
    { B e. HT087R3 |
      E. k e. ( RR \ { 0 } )
        B = ( HT087Scale k A )
    }
  $.
$}

${
  $d A B $.

  ht087-pplane-definition $a |- HT087PPlane =
    { A |
      E. B e. HT087R3
        (
          B =/= <. 0 , <. 0 , 0 >. >.
          /\
          A = ( HT087HClass B )
        )
    }
  $.
$}

ht087-det-definition $a |- ( HT087Det A B C ) =
  (
    (
      ( HT087X A )
      x.
      (
        (
          ( HT087PY B ) x. ( HT087Z C )
        )
        -
        (
          ( HT087Z B ) x. ( HT087PY C )
        )
      )
    )
    -
    (
      ( HT087PY A )
      x.
      (
        (
          ( HT087X B ) x. ( HT087Z C )
        )
        -
        (
          ( HT087Z B ) x. ( HT087X C )
        )
      )
    )
  )
  +
  (
    ( HT087Z A )
    x.
    (
      (
        ( HT087X B ) x. ( HT087PY C )
      )
      -
      (
        ( HT087PY B ) x. ( HT087X C )
      )
    )
  )
$.

${
  $d A B C p q r $.

  ht087-projective-collinearity-definition $a |- (
    ( HT087PCol A B C )
    <->
    E. p e. A
    E. q e. B
    E. r e. C
      ( ( HT087Det p q r ) = 0 )
  ) $.
$}

ht087-affine-collinearity-definition $a |- (
  ( HT087ACol A B C )
  <->
  (
    (
      ( ( HT087X B ) - ( HT087X A ) )
      x.
      ( ( HT087Y C ) - ( HT087Y A ) )
    )
    =
    (
      ( ( HT087Y B ) - ( HT087Y A ) )
      x.
      ( ( HT087X C ) - ( HT087X A ) )
    )
  )
) $.

ht087-triangle-definition $a |- (
  ( HT087Triangle A B C )
  <->
  -. ( HT087ACol A B C )
) $.

ht087-parallel-definition $a |- (
  ( HT087Parallel A B C D )
  <->
  (
    (
      ( ( HT087X B ) - ( HT087X A ) )
      x.
      ( ( HT087Y D ) - ( HT087Y C ) )
    )
    =
    (
      ( ( HT087Y B ) - ( HT087Y A ) )
      x.
      ( ( HT087X D ) - ( HT087X C ) )
    )
  )
) $.

ht087-projective-nondegeneracy-definition $a |- (
  ( HT087PND A B C D E F P Q R S )
  <->
  (
    -. ( HT087PCol D B S )
    /\
    (
      -. ( HT087PCol A P C )
      /\
      (
        -. ( HT087PCol A P R )
        /\
        (
          -. ( HT087PCol A C B )
          /\
          (
            -. ( HT087PCol A B R )
            /\
            (
              -. ( HT087PCol F P D )
              /\
              (
                -. ( HT087PCol F P B )
                /\
                (
                  -. ( HT087PCol F P E )
                  /\
                  (
                    -. ( HT087PCol F D S )
                    /\
                    (
                      -. ( HT087PCol F D E )
                      /\
                      (
                        -. ( HT087PCol P C D )
                        /\
                        (
                          -. ( HT087PCol P C B )
                          /\
                          (
                            -. ( HT087PCol P D R )
                            /\
                            (
                              -. ( HT087PCol P B Q )
                              /\
                              (
                                -. ( HT087PCol P Q E )
                                /\
                                (
                                  -. ( HT087PCol C B S )
                                  /\
                                  -. ( HT087PCol D Q E )
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
    )
  )
) $.

ht087-projective-configuration-definition $a |- (
  ( HT087PConfig A B C D E F P Q R S )
  <->
  (
    ( HT087PCol P D A )
    /\
    (
      ( HT087PCol P B E )
      /\
      (
        ( HT087PCol P F C )
        /\
        (
          ( HT087PCol B C Q )
          /\
          (
            ( HT087PCol E F Q )
            /\
            (
              ( HT087PCol A R C )
              /\
              (
                ( HT087PCol D F R )
                /\
                (
                  ( HT087PCol B S A )
                  /\
                  ( HT087PCol D S E )
                )
              )
            )
          )
        )
      )
    )
  )
) $.

${
  $d A B C D E F P Q R S $.

  hundred-theorems-087-desargues-projective $a |- (
    A. A e. HT087PPlane
    A. B e. HT087PPlane
    A. C e. HT087PPlane
    A. D e. HT087PPlane
    A. E e. HT087PPlane
    A. F e. HT087PPlane
    A. P e. HT087PPlane
    A. Q e. HT087PPlane
    A. R e. HT087PPlane
    A. S e. HT087PPlane
      (
        ( HT087PND A B C D E F P Q R S )
        ->
        (
          ( HT087PConfig A B C D E F P Q R S )
          ->
          ( HT087PCol Q S R )
        )
      )
  ) $.
$}

ht087-affine-hypotheses-definition $a |- (
  ( HT087AffineHyp A B C D E F S )
  <->
  (
    C =/= F
    /\
    (
      B =/= E
      /\
      (
        C =/= S
        /\
        (
          B =/= S
          /\
          (
            F =/= S
            /\
            (
              E =/= S
              /\
              (
                D =/= E
                /\
                (
                  D =/= F
                  /\
                  (
                    B =/= C
                    /\
                    (
                      E =/= F
                      /\
                      (
                        ( HT087Triangle A D B )
                        /\
                        (
                          ( HT087Triangle A D C )
                          /\
                          (
                            ( HT087ACol A D S )
                            /\
                            (
                              ( HT087ACol B E S )
                              /\
                              (
                                ( HT087ACol C F S )
                                /\
                                (
                                  ( HT087Parallel A B D E )
                                  /\
                                  ( HT087Parallel A C D F )
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
    )
  )
) $.

${
  $d A B C D E F S $.

  hundred-theorems-087-desargues-affine $a |- (
    A. A e. HT087R2
    A. B e. HT087R2
    A. C e. HT087R2
    A. D e. HT087R2
    A. E e. HT087R2
    A. F e. HT087R2
    A. S e. HT087R2
      (
        ( HT087AffineHyp A B C D E F S )
        ->
        ( HT087Parallel B C E F )
      )
  ) $.
$}
