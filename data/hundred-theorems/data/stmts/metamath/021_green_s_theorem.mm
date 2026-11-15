$(
  Statement-only formalization of "Green's Theorem" from Hundred Theorems item 021. It states
  the positively oriented planar curl theorem for an absolutely continuous closed curve and a
  continuously differentiable real vector field on an open neighborhood of the curve and its
  inside. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The Euclidean plane is identified isometrically with CC by (x,y) |-> x + i y. The source
  vector field f is represented by its real component functions P and Q, with

      P(z) = (f(z))_2,  Q(z) = (f(z))_1.

  Consequently the boundary integrand is P dx + Q dy and the interior integrand is
  partial_x Q - partial_y P, exactly the component ordering in GREEN_THEOREM_CURL.

  Every analytic notion introduced below is a conservative abbreviation over set.mm:

  * HT021AC uses the standard characterization of absolute continuity as an indefinite
    Lebesgue integral of an L^1 derivative.
  * HT021Inside is the union of the bounded connected components of the complement of the
    curve image in the standard complex topology.
  * HT021Dx and HT021Dy use set.mm's real derivative RR _D on coordinate slices. Their zero
    fallback is irrelevant on U, where HT021C1 explicitly requires all four derivatives.
  * HT021Wind1 is the defining contour-integral equation integral g'(t)/(g(t)-z) dt = 2*pi*i.
  * HT021PlaneIntegral is an iterated Lebesgue integral of the zero extension to RR x RR.
    Under the stated hypotheses the inside is bounded with negligible boundary and the curl
    is continuous, so this is the same planar integral as the source gauge integral.
  * HT021LineIntegral is the Lebesgue integral of the explicitly defined boundary integrand.
    Absolute continuity makes it equivalent to the source path integral.

  The final assertion is an unproved $a statement. The two integral predicates include the
  source integrability conclusions as well as the common integral value.
$)

$c HT021AC HT021Inside HT021D HT021Dx HT021Dy HT021C1 $.
$c HT021WindIntegrand HT021Wind1 HT021Line HT021Curl $.
$c HT021PlaneIntegrand HT021Row HT021PlaneIntegral HT021LineIntegral $.

ht021-ac-syntax $a wff ( HT021AC G ) $.
ht021-inside-syntax $a class ( HT021Inside G ) $.
ht021-d-syntax $a class ( HT021D G T ) $.
ht021-dx-syntax $a class ( HT021Dx P Z ) $.
ht021-dy-syntax $a class ( HT021Dy P Z ) $.
ht021-c1-syntax $a wff ( HT021C1 P Q U ) $.
ht021-wind-integrand-syntax $a class ( HT021WindIntegrand G Z T ) $.
ht021-wind1-syntax $a wff ( HT021Wind1 G Z ) $.
ht021-line-syntax $a class ( HT021Line P Q G T ) $.
ht021-curl-syntax $a class ( HT021Curl P Q Z ) $.
ht021-plane-integrand-syntax $a class ( HT021PlaneIntegrand H S X Y ) $.
ht021-row-syntax $a class ( HT021Row H S X ) $.
ht021-plane-integral-syntax $a wff ( HT021PlaneIntegral H S C ) $.
ht021-line-integral-syntax $a wff ( HT021LineIntegral P Q G C ) $.

${
  $d h t x G $.

  ht021-ac-definition $a |- (
    ( HT021AC G )
    <->
    (
      G : ( 0 [,] 1 ) --> CC
      /\
      E. h
        (
          ( h : RR --> CC /\ h e. L^1 )
          /\
          A. t e. ( 0 [,] 1 )
            ( G ` t ) =
              ( ( G ` 0 ) + S. ( 0 [,] t ) ( h ` x ) _d x )
        )
    )
  ) $.
$}

${
  $d c r w z G $.

  ht021-inside-definition $a |- (
    ( HT021Inside G )
    =
    { z e. ( CC \ ran G ) |
      E. r e. RR+
        A. w e.
          U. { c e. ~P ( CC \ ran G ) |
            (
              z e. c
              /\
              (
                (
                  ( ( TopOpen ` CCfld ) |`t ( CC \ ran G ) )
                  |`t c
                )
                e. Conn
              )
            )
          }
          ( ( abs ` w ) < r )
    }
  ) $.
$}

${
  $d G T $.

  ht021-d-definition $a |- (
    ( HT021D G T )
    =
    if
      (
        T e. dom ( RR _D G ) ,
        ( ( RR _D G ) ` T ) ,
        0
      )
  ) $.
$}

${
  $d r P Z $.

  ht021-dx-definition $a |- (
    ( HT021Dx P Z )
    =
    if
      (
        ( Re ` Z ) e.
          dom
            (
              RR _D
                ( r e. RR |->
                  ( P ` ( r + ( _i x. ( Im ` Z ) ) ) )
                )
            ) ,
        (
          (
            RR _D
              ( r e. RR |->
                ( P ` ( r + ( _i x. ( Im ` Z ) ) ) )
              )
          )
          ` ( Re ` Z )
        ) ,
        0
      )
  ) $.
$}

${
  $d r P Z $.

  ht021-dy-definition $a |- (
    ( HT021Dy P Z )
    =
    if
      (
        ( Im ` Z ) e.
          dom
            (
              RR _D
                ( r e. RR |->
                  ( P ` ( ( Re ` Z ) + ( _i x. r ) ) )
                )
            ) ,
        (
          (
            RR _D
              ( r e. RR |->
                ( P ` ( ( Re ` Z ) + ( _i x. r ) ) )
              )
          )
          ` ( Im ` Z )
        ) ,
        0
      )
  ) $.
$}

${
  $d r z P Q U $.

  ht021-c1-definition $a |- (
    ( HT021C1 P Q U )
    <->
    (
      (
        U e. ( TopOpen ` CCfld )
        /\
        ( P : CC --> RR /\ Q : CC --> RR )
      )
      /\
      (
        A. z e. U
          (
            (
              ( Re ` z ) e.
                dom
                  (
                    RR _D
                      ( r e. RR |->
                        ( P ` ( r + ( _i x. ( Im ` z ) ) ) )
                      )
                  )
              /\
              ( Im ` z ) e.
                dom
                  (
                    RR _D
                      ( r e. RR |->
                        ( P ` ( ( Re ` z ) + ( _i x. r ) ) )
                      )
                  )
            )
            /\
            (
              ( Re ` z ) e.
                dom
                  (
                    RR _D
                      ( r e. RR |->
                        ( Q ` ( r + ( _i x. ( Im ` z ) ) ) )
                      )
                  )
              /\
              ( Im ` z ) e.
                dom
                  (
                    RR _D
                      ( r e. RR |->
                        ( Q ` ( ( Re ` z ) + ( _i x. r ) ) )
                      )
                  )
            )
          )
        /\
        (
          (
            ( z e. U |-> ( HT021Dx P z ) ) e. ( U -cn-> CC )
            /\
            ( z e. U |-> ( HT021Dy P z ) ) e. ( U -cn-> CC )
          )
          /\
          (
            ( z e. U |-> ( HT021Dx Q z ) ) e. ( U -cn-> CC )
            /\
            ( z e. U |-> ( HT021Dy Q z ) ) e. ( U -cn-> CC )
          )
        )
      )
    )
  ) $.
$}

${
  $d G Z T $.

  ht021-wind-integrand-definition $a |- (
    ( HT021WindIntegrand G Z T )
    =
    ( ( HT021D G T ) / ( ( G ` T ) - Z ) )
  ) $.
$}

${
  $d t G Z $.

  ht021-wind1-definition $a |- (
    ( HT021Wind1 G Z )
    <->
    (
      (
        t e. RR |->
          if
            (
              t e. ( 0 [,] 1 ) ,
              ( HT021WindIntegrand G Z t ) ,
              0
            )
      )
      e. L^1
      /\
      S. ( 0 [,] 1 ) ( HT021WindIntegrand G Z t ) _d t
        = ( ( 2 x. _pi ) x. _i )
    )
  ) $.
$}

${
  $d P Q G T $.

  ht021-line-definition $a |- (
    ( HT021Line P Q G T )
    =
    (
      (
        ( P ` ( G ` T ) )
        x.
        ( Re ` ( HT021D G T ) )
      )
      +
      (
        ( Q ` ( G ` T ) )
        x.
        ( Im ` ( HT021D G T ) )
      )
    )
  ) $.
$}

${
  $d P Q Z $.

  ht021-curl-definition $a |- (
    ( HT021Curl P Q Z )
    =
    ( ( HT021Dx Q Z ) - ( HT021Dy P Z ) )
  ) $.
$}

${
  $d H S X Y $.

  ht021-plane-integrand-definition $a |- (
    ( HT021PlaneIntegrand H S X Y )
    =
    if
      (
        ( X + ( _i x. Y ) ) e. S ,
        ( H ` ( X + ( _i x. Y ) ) ) ,
        0
      )
  ) $.
$}

${
  $d y H S X $.

  ht021-row-definition $a |- (
    ( HT021Row H S X )
    =
    S. RR ( HT021PlaneIntegrand H S X y ) _d y
  ) $.
$}

${
  $d x y H S C $.

  ht021-plane-integral-definition $a |- (
    ( HT021PlaneIntegral H S C )
    <->
    (
      H : CC --> CC
      /\
      (
        A. x e. RR
          ( y e. RR |-> ( HT021PlaneIntegrand H S x y ) ) e. L^1
        /\
        (
          ( x e. RR |-> ( HT021Row H S x ) ) e. L^1
          /\
          C = S. RR ( HT021Row H S x ) _d x
        )
      )
    )
  ) $.
$}

${
  $d t P Q G C $.

  ht021-line-integral-definition $a |- (
    ( HT021LineIntegral P Q G C )
    <->
    (
      (
        t e. RR |->
          if
            (
              t e. ( 0 [,] 1 ) ,
              ( HT021Line P Q G t ) ,
              0
            )
      )
      e. L^1
      /\
      C = S. ( 0 [,] 1 ) ( HT021Line P Q G t ) _d t
    )
  ) $.
$}

${
  $d c z G P Q U $.

  hundred-theorems-021-green-theorem $a |- (
    (
      (
        ( HT021AC G )
        /\
        ( G ` 1 ) = ( G ` 0 )
      )
      /\
      (
        (
          A. z e. ( HT021Inside G )
            ( HT021Wind1 G z )
          /\
          ( ( ( HT021Inside G ) u. ran G ) C_ U )
        )
        /\
        ( HT021C1 P Q U )
      )
    )
    ->
    E. c e. CC
      (
        (
          HT021PlaneIntegral
            ( z e. CC |-> ( HT021Curl P Q z ) )
            ( HT021Inside G )
            c
        )
        /\
        ( HT021LineIntegral P Q G c )
      )
  ) $.
$}
