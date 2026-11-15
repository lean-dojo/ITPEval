$(
  Statement-only formalization of "Pascal's Hexagon Theorem" from Hundred
  Theorems item 028: Pascal collinearity for conics in the real projective
  and affine planes, its circle specialization, and the abstract
  projective-plane Pappus-to-hexamy formulation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The HOL Light domains are represented definitionally in set.mm.

  HT028R2 is RR X. RR. HT028R3 is RR X. ( RR X. RR ). A real projective
  point is an equivalence class of nonzero triples under multiplication by a
  nonzero real scalar. Projective collinearity is vanishing of the 3 by 3
  determinant for representatives, and affine/projective conics are exactly
  zero sets of nonzero real quadratic forms.

  For the Rocq formulation, P and L are explicit point and line carriers, I
  is an incidence relation, J chooses a line through two points, and N chooses
  an intersection point of two lines. HT028Plane states the projective-plane
  existence, uniqueness, and nondegeneracy laws and specifies both choices.

  The malformed HOL Light projective binder repeats x6 and leaves x7 free.
  The projective assertion below binds the seventh point, as required by its
  occurrences and by the correctly bound affine assertion.

  All final theorem declarations are unproved $a statements.
$)

$c
  HT028R2 HT028R3 HT028X HT028Y HT028PY HT028Z HT028Scale HT028HClass
  HT028PPlane HT028Det HT028ACol HT028PCol HT028APoly HT028PPoly
  HT028AConic HT028PConic HT028Circle HT028Distinct6 HT028AND
  HT028PND HT028AConfig HT028PConfig HT028Inc HT028AbsCol
  HT028Plane HT028OnInter HT028Hex HT028Pappus
$.

ht028-r2-syntax $a class HT028R2 $.
ht028-r3-syntax $a class HT028R3 $.
ht028-x-syntax $a class ( HT028X A ) $.
ht028-y-syntax $a class ( HT028Y A ) $.
ht028-py-syntax $a class ( HT028PY A ) $.
ht028-z-syntax $a class ( HT028Z A ) $.
ht028-scale-syntax $a class ( HT028Scale A B ) $.
ht028-hclass-syntax $a class ( HT028HClass A ) $.
ht028-pplane-syntax $a class HT028PPlane $.
ht028-det-syntax $a class ( HT028Det A B C ) $.
ht028-acol-syntax $a wff ( HT028ACol A B C ) $.
ht028-pcol-syntax $a wff ( HT028PCol A B C ) $.
ht028-apoly-syntax $a class ( HT028APoly A B C D E F G ) $.
ht028-ppoly-syntax $a class ( HT028PPoly A B C D E F G ) $.
ht028-aconic-syntax $a wff ( HT028AConic A ) $.
ht028-pconic-syntax $a wff ( HT028PConic A ) $.
ht028-circle-syntax $a wff ( HT028Circle A B C ) $.
ht028-distinct6-syntax $a wff ( HT028Distinct6 A B C D E F ) $.
ht028-and-syntax $a wff ( HT028AND A B C D E F ) $.
ht028-pnd-syntax $a wff ( HT028PND A B C D E F ) $.
ht028-aconfig-syntax
  $a wff ( HT028AConfig A B C D E F G H I J ) $.
ht028-pconfig-syntax
  $a wff ( HT028PConfig A B C D E F G H I J ) $.
ht028-inc-syntax $a wff ( HT028Inc A B C ) $.
ht028-abscol-syntax $a wff ( HT028AbsCol A B C D E ) $.
ht028-plane-syntax $a wff ( HT028Plane A B C D E ) $.
ht028-oninter-syntax
  $a wff ( HT028OnInter A B C D E F G ) $.
ht028-hex-syntax
  $a wff ( HT028Hex A B C D E F G H I J ) $.
ht028-pappus-syntax $a wff ( HT028Pappus A B C D ) $.

ht028-r2-definition $a |- HT028R2 = ( RR X. RR ) $.

ht028-r3-definition $a |- HT028R3 = ( RR X. ( RR X. RR ) ) $.

ht028-x-definition $a |- ( HT028X A ) = ( 1st ` A ) $.

ht028-y-definition $a |- ( HT028Y A ) = ( 2nd ` A ) $.

ht028-py-definition $a |- ( HT028PY A ) = ( 1st ` ( 2nd ` A ) ) $.

ht028-z-definition $a |- ( HT028Z A ) = ( 2nd ` ( 2nd ` A ) ) $.

ht028-scale-definition $a |- ( HT028Scale A B ) =
  <.
    ( A x. ( HT028X B ) )
    ,
    <.
      ( A x. ( HT028PY B ) )
      ,
      ( A x. ( HT028Z B ) )
    >.
  >.
$.

${
  $d A b k $.
  ht028-hclass-definition $a |- ( HT028HClass A ) =
    { b e. HT028R3 |
      E. k e. ( RR \ { 0 } )
        b = ( HT028Scale k A )
    }
  $.
$}

${
  $d a b $.
  ht028-pplane-definition $a |- HT028PPlane =
    { a |
      E. b e. HT028R3
        (
          b =/= <. 0 , <. 0 , 0 >. >.
          /\
          a = ( HT028HClass b )
        )
    }
  $.
$}

ht028-det-definition $a |- ( HT028Det A B C ) =
  (
    (
      ( HT028X A )
      x.
      (
        (
          ( HT028PY B ) x. ( HT028Z C )
        )
        -
        (
          ( HT028Z B ) x. ( HT028PY C )
        )
      )
    )
    -
    (
      ( HT028PY A )
      x.
      (
        (
          ( HT028X B ) x. ( HT028Z C )
        )
        -
        (
          ( HT028Z B ) x. ( HT028X C )
        )
      )
    )
  )
  +
  (
    ( HT028Z A )
    x.
    (
      (
        ( HT028X B ) x. ( HT028PY C )
      )
      -
      (
        ( HT028PY B ) x. ( HT028X C )
      )
    )
  )
$.

ht028-affine-collinearity-definition $a |- (
  ( HT028ACol A B C )
  <->
  (
    (
      (
        ( HT028X B ) - ( HT028X A )
      )
      x.
      (
        ( HT028Y C ) - ( HT028Y A )
      )
    )
    =
    (
      (
        ( HT028Y B ) - ( HT028Y A )
      )
      x.
      (
        ( HT028X C ) - ( HT028X A )
      )
    )
  )
) $.

${
  $d A B C p q r $.
  ht028-projective-collinearity-definition $a |- (
    ( HT028PCol A B C )
    <->
    E. p e. A
    E. q e. B
    E. r e. C
      ( ( HT028Det p q r ) = 0 )
  ) $.
$}

ht028-affine-polynomial-definition $a |- (
  HT028APoly A B C D E F G
) =
  (
    (
      ( A x. ( ( HT028X G ) ^ 2 ) )
      +
      ( B x. ( ( HT028Y G ) ^ 2 ) )
    )
    +
    (
      ( C x. ( ( HT028X G ) x. ( HT028Y G ) ) )
      +
      (
        ( D x. ( HT028X G ) )
        +
        (
          ( E x. ( HT028Y G ) )
          +
          F
        )
      )
    )
  )
$.

ht028-projective-polynomial-definition $a |- (
  HT028PPoly A B C D E F G
) =
  (
    (
      ( A x. ( ( HT028X G ) ^ 2 ) )
      +
      ( B x. ( ( HT028PY G ) ^ 2 ) )
    )
    +
    (
      ( C x. ( ( HT028Z G ) ^ 2 ) )
      +
      (
        ( D x. ( ( HT028X G ) x. ( HT028PY G ) ) )
        +
        (
          ( E x. ( ( HT028X G ) x. ( HT028Z G ) ) )
          +
          ( F x. ( ( HT028PY G ) x. ( HT028Z G ) ) )
        )
      )
    )
  )
$.

${
  $d K a b c d e f p $.
  ht028-affine-conic-definition $a |- (
    ( HT028AConic K )
    <->
    E. a e. RR
    E. b e. RR
    E. c e. RR
    E. d e. RR
    E. e e. RR
    E. f e. RR
      (
        -.
        (
          a = 0
          /\
          (
            b = 0
            /\
            (
              c = 0
              /\
              (
                d = 0
                /\
                (
                  e = 0
                  /\
                  f = 0
                )
              )
            )
          )
        )
        /\
        K =
        { p e. HT028R2 |
          ( HT028APoly a b c d e f p ) = 0
        }
      )
  ) $.
$}

${
  $d K p a b c d e f v $.
  ht028-projective-conic-definition $a |- (
    ( HT028PConic K )
    <->
    E. a e. RR
    E. b e. RR
    E. c e. RR
    E. d e. RR
    E. e e. RR
    E. f e. RR
      (
        -.
        (
          a = 0
          /\
          (
            b = 0
            /\
            (
              c = 0
              /\
              (
                d = 0
                /\
                (
                  e = 0
                  /\
                  f = 0
                )
              )
            )
          )
        )
        /\
        K =
        { p e. HT028PPlane |
          E. v e. p
            ( HT028PPoly a b c d e f v ) = 0
        }
      )
  ) $.
$}

ht028-circle-definition $a |- (
  ( HT028Circle A B C )
  <->
  (
    sqrt
    `
    (
      (
        (
          ( HT028X B ) - ( HT028X A )
        )
        ^ 2
      )
      +
      (
        (
          ( HT028Y B ) - ( HT028Y A )
        )
        ^ 2
      )
    )
  )
  =
  C
) $.

ht028-distinct-six-definition $a |- (
  ( HT028Distinct6 A B C D E F )
  <->
  (
    A =/= B
    /\
    (
      A =/= C
      /\
      (
        A =/= D
        /\
        (
          A =/= E
          /\
          (
            A =/= F
            /\
            (
              B =/= C
              /\
              (
                B =/= D
                /\
                (
                  B =/= E
                  /\
                  (
                    B =/= F
                    /\
                    (
                      C =/= D
                      /\
                      (
                        C =/= E
                        /\
                        (
                          C =/= F
                          /\
                          (
                            D =/= E
                            /\
                            (
                              D =/= F
                              /\
                              E =/= F
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

ht028-affine-nondegenerate-definition $a |- (
  ( HT028AND A B C D E F )
  <->
  (
    -. ( HT028ACol A B D )
    /\
    (
      -. ( HT028ACol A B E )
      /\
      (
        -. ( HT028ACol A B F )
        /\
        (
          -. ( HT028ACol A C D )
          /\
          (
            -. ( HT028ACol A C E )
            /\
            (
              -. ( HT028ACol A C F )
              /\
              (
                -. ( HT028ACol B C D )
                /\
                (
                  -. ( HT028ACol B C E )
                  /\
                  (
                    -. ( HT028ACol B C F )
                    /\
                    (
                      -. ( HT028ACol D E A )
                      /\
                      (
                        -. ( HT028ACol D E B )
                        /\
                        (
                          -. ( HT028ACol D E C )
                          /\
                          (
                            -. ( HT028ACol D F A )
                            /\
                            (
                              -. ( HT028ACol D F B )
                              /\
                              (
                                -. ( HT028ACol D F C )
                                /\
                                (
                                  -. ( HT028ACol E F A )
                                  /\
                                  (
                                    -. ( HT028ACol E F B )
                                    /\
                                    -. ( HT028ACol E F C )
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
  )
) $.

ht028-projective-nondegenerate-definition $a |- (
  ( HT028PND A B C D E F )
  <->
  (
    -. ( HT028PCol A B D )
    /\
    (
      -. ( HT028PCol A B E )
      /\
      (
        -. ( HT028PCol A B F )
        /\
        (
          -. ( HT028PCol A C D )
          /\
          (
            -. ( HT028PCol A C E )
            /\
            (
              -. ( HT028PCol A C F )
              /\
              (
                -. ( HT028PCol B C D )
                /\
                (
                  -. ( HT028PCol B C E )
                  /\
                  (
                    -. ( HT028PCol B C F )
                    /\
                    (
                      -. ( HT028PCol D E A )
                      /\
                      (
                        -. ( HT028PCol D E B )
                        /\
                        (
                          -. ( HT028PCol D E C )
                          /\
                          (
                            -. ( HT028PCol D F A )
                            /\
                            (
                              -. ( HT028PCol D F B )
                              /\
                              (
                                -. ( HT028PCol D F C )
                                /\
                                (
                                  -. ( HT028PCol E F A )
                                  /\
                                  (
                                    -. ( HT028PCol E F B )
                                    /\
                                    -. ( HT028PCol E F C )
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
  )
) $.

ht028-affine-config-definition $a |- (
  ( HT028AConfig K A B C D E F G H I )
  <->
  (
    ( HT028AConic K )
    /\
    (
      A e. K
      /\
      (
        B e. K
        /\
        (
          C e. K
          /\
          (
            D e. K
            /\
            (
              E e. K
              /\
              (
                F e. K
                /\
                (
                  ( HT028ACol A I E )
                  /\
                  (
                    ( HT028ACol A H F )
                    /\
                    (
                      ( HT028ACol B I D )
                      /\
                      (
                        ( HT028ACol B G F )
                        /\
                        (
                          ( HT028ACol C H D )
                          /\
                          ( HT028ACol C G E )
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

ht028-projective-config-definition $a |- (
  ( HT028PConfig K A B C D E F G H I )
  <->
  (
    ( HT028PConic K )
    /\
    (
      A e. K
      /\
      (
        B e. K
        /\
        (
          C e. K
          /\
          (
            D e. K
            /\
            (
              E e. K
              /\
              (
                F e. K
                /\
                (
                  ( HT028PCol A I E )
                  /\
                  (
                    ( HT028PCol A H F )
                    /\
                    (
                      ( HT028PCol B I D )
                      /\
                      (
                        ( HT028PCol B G F )
                        /\
                        (
                          ( HT028PCol C H D )
                          /\
                          ( HT028PCol C G E )
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

$(
  Pascal in the concrete real projective plane.
$)
${
  $d a b c d e f g h i k $.

hundred-pascal-projective $a |- A. k
  A. a e. HT028PPlane
  A. b e. HT028PPlane
  A. c e. HT028PPlane
  A. d e. HT028PPlane
  A. e e. HT028PPlane
  A. f e. HT028PPlane
  A. g e. HT028PPlane
  A. h e. HT028PPlane
  A. i e. HT028PPlane
    (
      ( HT028PND a b c d e f )
      ->
      (
        ( HT028PConfig k a b c d e f g h i )
        ->
        ( HT028PCol g h i )
      )
    )
$.
$}

$(
  Pascal in the real affine plane.
$)
${
  $d a b c d e f g h i k $.

hundred-pascal-affine $a |- A. k
  A. a e. HT028R2
  A. b e. HT028R2
  A. c e. HT028R2
  A. d e. HT028R2
  A. e e. HT028R2
  A. f e. HT028R2
  A. g e. HT028R2
  A. h e. HT028R2
  A. i e. HT028R2
    (
      ( HT028AND a b c d e f )
      ->
      (
        ( HT028AConfig k a b c d e f g h i )
        ->
        ( HT028ACol g h i )
      )
    )
$.
$}

$(
  The circle specialization, with the six vertices pairwise distinct.
$)
${
  $d a b c d e f g h i o r $.

hundred-pascal-affine-circle $a |- A. o e. HT028R2
  A. r e. RR
  A. a e. HT028R2
  A. b e. HT028R2
  A. c e. HT028R2
  A. d e. HT028R2
  A. e e. HT028R2
  A. f e. HT028R2
  A. g e. HT028R2
  A. h e. HT028R2
  A. i e. HT028R2
    (
      ( HT028Distinct6 a b c d e f )
      ->
      (
        (
          ( HT028Circle o a r )
          /\
          (
            ( HT028Circle o b r )
            /\
            (
              ( HT028Circle o c r )
              /\
              (
                ( HT028Circle o d r )
                /\
                (
                  ( HT028Circle o e r )
                  /\
                  (
                    ( HT028Circle o f r )
                    /\
                    (
                      ( HT028ACol a i e )
                      /\
                      (
                        ( HT028ACol a h f )
                        /\
                        (
                          ( HT028ACol b i d )
                          /\
                          (
                            ( HT028ACol b g f )
                            /\
                            (
                              ( HT028ACol c h d )
                              /\
                              ( HT028ACol c g e )
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
        ( HT028ACol g h i )
      )
    )
$.
$}

ht028-incidence-definition $a |- (
  ( HT028Inc A B I )
  <->
  <. A , B >. e. I
) $.

${
  $d A B C l L I $.
  ht028-abstract-collinearity-definition $a |- (
    ( HT028AbsCol L I A B C )
    <->
    E. l e. L
      (
        ( HT028Inc A l I )
        /\
        (
          ( HT028Inc B l I )
          /\
          ( HT028Inc C l I )
        )
      )
  ) $.
$}

${
  $d a b c l m P L I J N $.
  ht028-plane-definition $a |- (
    ( HT028Plane P L I J N )
    <->
    (
      I C_ ( P X. L )
      /\
      (
        J : ( P X. P ) --> L
        /\
        (
          N : ( L X. L ) --> P
          /\
          (
            (
              A. a e. P
              A. b e. P
                (
                  ( HT028Inc a ( J ` <. a , b >. ) I )
                  /\
                  ( HT028Inc b ( J ` <. a , b >. ) I )
                )
            )
            /\
            (
              (
                A. l e. L
                A. m e. L
                  (
                    ( HT028Inc ( N ` <. l , m >. ) l I )
                    /\
                    ( HT028Inc ( N ` <. l , m >. ) m I )
                  )
              )
              /\
              (
                (
                  A. a e. P
                  A. b e. P
                  A. l e. L
                  A. m e. L
                    (
                      (
                        a =/= b
                        /\
                        (
                          ( HT028Inc a l I )
                          /\
                          (
                            ( HT028Inc b l I )
                            /\
                            (
                              ( HT028Inc a m I )
                              /\
                              ( HT028Inc b m I )
                            )
                          )
                        )
                      )
                      ->
                      l = m
                    )
                )
                /\
                (
                  (
                    A. l e. L
                    A. m e. L
                    A. a e. P
                    A. b e. P
                      (
                        (
                          l =/= m
                          /\
                          (
                            ( HT028Inc a l I )
                            /\
                            (
                              ( HT028Inc a m I )
                              /\
                              (
                                ( HT028Inc b l I )
                                /\
                                ( HT028Inc b m I )
                              )
                            )
                          )
                        )
                        ->
                        a = b
                      )
                  )
                  /\
                  (
                    (
                      E. a e. P
                      E. b e. P
                      E. c e. P
                        (
                          a =/= b
                          /\
                          (
                            b =/= c
                            /\
                            (
                              a =/= c
                              /\
                              -. ( HT028AbsCol L I a b c )
                            )
                          )
                        )
                    )
                    /\
                    (
                      A. l e. L
                      E. a e. P
                      E. b e. P
                      E. c e. P
                        (
                          a =/= b
                          /\
                          (
                            b =/= c
                            /\
                            (
                              a =/= c
                              /\
                              (
                                ( HT028Inc a l I )
                                /\
                                (
                                  ( HT028Inc b l I )
                                  /\
                                  ( HT028Inc c l I )
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
$}

ht028-on-intersection-definition $a |- (
  ( HT028OnInter L I A B C D E )
  <->
  (
    ( HT028AbsCol L I A B C )
    /\
    ( HT028AbsCol L I A D E )
  )
) $.

ht028-hexamy-definition $a |- (
  ( HT028Hex L I J N A B C D E F )
  <->
  (
    ( HT028Distinct6 A B C D E F )
    /\
    (
      HT028AbsCol
      L
      I
      ( N ` <. ( J ` <. B , C >. ) , ( J ` <. E , F >. ) >. )
      ( N ` <. ( J ` <. C , D >. ) , ( J ` <. F , A >. ) >. )
      ( N ` <. ( J ` <. A , B >. ) , ( J ` <. D , E >. ) >. )
    )
  )
) $.

${
  $d a b c d e f g h k P L I J $.
  ht028-pappus-strong-definition $a |- (
    ( HT028Pappus P L I J )
    <->
    A. a e. P
    A. b e. P
    A. c e. P
    A. d e. P
    A. e e. P
    A. f e. P
    A. g e. P
    A. h e. P
    A. k e. P
      (
        (
          ( HT028Distinct6 a b c d e f )
          \/
          (
            ( J ` <. a , e >. ) =/= ( J ` <. d , b >. )
            /\
            (
              a =/= e
              /\
              (
                d =/= b
                /\
                (
                  ( J ` <. b , f >. ) =/= ( J ` <. e , c >. )
                  /\
                  (
                    b =/= f
                    /\
                    (
                      e =/= c
                      /\
                      (
                        ( J ` <. a , f >. ) =/= ( J ` <. d , c >. )
                        /\
                        (
                          a =/= f
                          /\
                          d =/= c
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
        (
          ( HT028AbsCol L I a b c )
          ->
          (
            ( HT028AbsCol L I d e f )
            ->
            (
              ( HT028OnInter L I g a e d b )
              ->
              (
                ( HT028OnInter L I h b f e c )
                ->
                (
                  ( HT028OnInter L I k a f d c )
                  ->
                  ( HT028AbsCol L I g h k )
                )
              )
            )
          )
        )
      )
  ) $.
$}

$(
  Rocq's hexamy_prop over every explicitly axiomatized abstract projective
  plane and every pair of specified line/intersection choice functions.
$)
${
  $d a b c d e f i j l n p $.

hundred-pappus-implies-hexamy $a |- A. p A. l A. i A. j A. n
  (
    ( HT028Plane p l i j n )
    ->
    (
      ( HT028Pappus p l i j )
      ->
      A. a e. p
      A. b e. p
      A. c e. p
      A. d e. p
      A. e e. p
      A. f e. p
        (
          ( j ` <. c , d >. ) =/= ( j ` <. a , f >. )
          ->
          (
            ( j ` <. b , c >. ) =/= ( j ` <. e , f >. )
            ->
            (
              ( j ` <. a , b >. ) =/= ( j ` <. d , e >. )
              ->
              (
                ( j ` <. a , c >. ) =/= ( j ` <. e , f >. )
                ->
                (
                  ( j ` <. b , f >. ) =/= ( j ` <. c , d >. )
                  ->
                  (
                    ( HT028Hex l i j n a b c d e f )
                    ->
                    ( HT028Hex l i j n b a c d e f )
                  )
                )
              )
            )
          )
        )
    )
  )
$.
$}
