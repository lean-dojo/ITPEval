$(
  Statement-only formalization of Thousand Theorems corpus artifact Q338886
  (thousand-theorems__metamath__Q338886), "Divergence theorem": for a
  continuous vector field on an arbitrary finite-dimensional real box,
  Frechet differentiable off a countable subset of the interior with
  integrable divergence, the volume integral of the divergence equals the
  signed sum of the integrals over the coordinate faces. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The positive integer N represents n+1, and D = 0 ..^ N represents
  Fin (n+1). Q338886RealNorm and Q338886VecNorm use finite l1 product norms
  on RR^D and Base(W)^D. These norms induce the same topologies and Frechet
  derivative predicate as Lean's finite product norms.

  Q338886Open is the norm topology on RR^D. Q338886Volume is the normalized
  translation-invariant locally finite Borel measure on this space, hence the
  finite product Lebesgue measure used by Lean. The same definition applies
  when D has one coordinate removed; for N = 1 the resulting zero-dimensional
  space is the singleton with mass one.

  Q338886ContinuousLinear and Q338886HasFDerivAt explicitly render continuous
  real-linear maps and Frechet derivatives. Q338886Divergence is the finite
  W-valued sum of the diagonal directional derivatives.

  Q338886Integrable uses the simple-function characterization of Bochner
  integrability, without imposing completeness on W. Q338886HasIntegral
  defines the integral value by L1-approximation with measurable finite-range
  functions. Q338886TotalIntegral has Lean's totalization: it is the unique
  such value when W is complete and the function is integrable, and zero
  otherwise.

  Removing i from D is canonically equivalent, by coordinate relabeling, to
  Fin n via Fin.succAbove i. Q338886Insert inserts the fixed coordinate, so
  Q338886FaceFunction and Q338886FaceBox are exactly the front and back face
  integrands and boxes in the canonical Lean statement.

  The final declaration is the single unproved corpus $a statement. Every
  preceding $a declaration is syntax or an explicit faithful definition, and
  this database contains no $p proof statement.
$)

$c Q338886RealSub Q338886VecSub Q338886RealNorm Q338886VecNorm
   Q338886OpenBall Q338886Open Q338886Box Q338886Interior
   Q338886Basis Q338886Insert Q338886FaceBox
   Q338886Translate Q338886Measure Q338886UnitBox
   Q338886NormalizedHaar Q338886Volume
   Q338886ContinuousLinear Q338886HasFDerivAt Q338886ContinuousOn
   Q338886Divergence Q338886Simple Q338886SimpleIntegral
   Q338886LIntegral Q338886Tendsto Q338886AEStrong
   Q338886Integrable Q338886Diff Q338886L1Distance
   Q338886HasIntegral Q338886Restrict Q338886IntegrableOn
   Q338886TotalIntegral Q338886IntegralOn Q338886FaceFunction $.

q338886-real-sub-syntax
  $a class ( Q338886RealSub D x y ) $.
q338886-vec-sub-syntax
  $a class ( Q338886VecSub D W u v ) $.
q338886-real-norm-syntax
  $a class ( Q338886RealNorm D x ) $.
q338886-vec-norm-syntax
  $a class ( Q338886VecNorm D W u ) $.
q338886-open-ball-syntax
  $a class ( Q338886OpenBall D x r ) $.
q338886-open-syntax
  $a class ( Q338886Open D ) $.
q338886-box-syntax
  $a class ( Q338886Box D a b ) $.
q338886-interior-syntax
  $a class ( Q338886Interior D a b ) $.
q338886-basis-syntax
  $a class ( Q338886Basis D i ) $.
q338886-insert-syntax
  $a class ( Q338886Insert D i c y ) $.
q338886-face-box-syntax
  $a class ( Q338886FaceBox D a b i ) $.
q338886-translate-syntax
  $a class ( Q338886Translate D a A ) $.
q338886-measure-syntax
  $a class ( Q338886Measure M A ) $.
q338886-unit-box-syntax
  $a class ( Q338886UnitBox D ) $.
q338886-normalized-haar-syntax
  $a wff ( Q338886NormalizedHaar D M ) $.
q338886-volume-syntax
  $a class ( Q338886Volume D ) $.
q338886-continuous-linear-syntax
  $a wff ( Q338886ContinuousLinear D W L ) $.
q338886-has-fderiv-at-syntax
  $a wff ( Q338886HasFDerivAt D W F x L ) $.
q338886-continuous-on-syntax
  $a wff ( Q338886ContinuousOn D W F A ) $.
q338886-divergence-syntax
  $a class ( Q338886Divergence D W G x ) $.
q338886-simple-syntax
  $a wff ( Q338886Simple M G ) $.
q338886-simple-integral-syntax
  $a class ( Q338886SimpleIntegral M G ) $.
q338886-lintegral-syntax
  $a class ( Q338886LIntegral M H ) $.
q338886-tendsto-syntax
  $a wff ( Q338886Tendsto W S z ) $.
q338886-aestrong-syntax
  $a wff ( Q338886AEStrong M W H ) $.
q338886-integrable-syntax
  $a wff ( Q338886Integrable M W H ) $.
q338886-diff-syntax
  $a class ( Q338886Diff M W H K ) $.
q338886-l1-distance-syntax
  $a class ( Q338886L1Distance M W H K ) $.
q338886-has-integral-syntax
  $a wff ( Q338886HasIntegral M W H y ) $.
q338886-restrict-syntax
  $a class ( Q338886Restrict M W A H ) $.
q338886-integrable-on-syntax
  $a wff ( Q338886IntegrableOn M W A H ) $.
q338886-total-integral-syntax
  $a class ( Q338886TotalIntegral W M H ) $.
q338886-integral-on-syntax
  $a class ( Q338886IntegralOn W M A H ) $.
q338886-face-function-syntax
  $a class ( Q338886FaceFunction D W F i c ) $.

${
  $d D i x y $.

  q338886-real-sub-definition $a |- (
    Q338886RealSub D x y
  ) =
    ( i e. D |-> ( ( x ` i ) - ( y ` i ) ) )
  $.
$}

${
  $d D W i u v $.

  q338886-vec-sub-definition $a |- (
    Q338886VecSub D W u v
  ) =
    ( i e. D |->
      (
        ( u ` i )
        ( +g ` W )
        ( ( -g ` W ) ` ( v ` i ) )
      )
    )
  $.
$}

${
  $d D i x $.

  q338886-real-norm-definition $a |- (
    Q338886RealNorm D x
  ) =
    sum_ i e. D ( abs ` ( x ` i ) )
  $.
$}

${
  $d D W i u $.

  q338886-vec-norm-definition $a |- (
    Q338886VecNorm D W u
  ) =
    sum_ i e. D
      ( ( norm ` W ) ` ( u ` i ) )
  $.
$}

${
  $d D r x y $.

  q338886-open-ball-definition $a |- (
    Q338886OpenBall D x r
  ) = {
    y e. ( RR ^m D ) |
      ( Q338886RealNorm D ( Q338886RealSub D y x ) ) < r
  } $.
$}

${
  $d D U r x $.

  q338886-open-definition $a |- (
    Q338886Open D
  ) = {
    U e. ~P ( RR ^m D ) |
      A. x e. U
        E. r e. RR+
          ( Q338886OpenBall D x r ) C_ U
  } $.
$}

${
  $d D a b i x $.

  q338886-box-definition $a |- (
    Q338886Box D a b
  ) = {
    x e. ( RR ^m D ) |
      A. i e. D
        (
          ( a ` i ) <_ ( x ` i )
          /\
          ( x ` i ) <_ ( b ` i )
        )
  } $.
$}

${
  $d D a b i x $.

  q338886-interior-definition $a |- (
    Q338886Interior D a b
  ) = {
    x e. ( RR ^m D ) |
      A. i e. D
        (
          ( a ` i ) < ( x ` i )
          /\
          ( x ` i ) < ( b ` i )
        )
  } $.
$}

${
  $d D i j $.

  q338886-basis-definition $a |- (
    Q338886Basis D i
  ) =
    ( j e. D |-> if ( j = i , 1 , 0 ) )
  $.
$}

${
  $d D c i j y $.

  q338886-insert-definition $a |- (
    Q338886Insert D i c y
  ) =
    ( j e. D |-> if ( j = i , c , ( y ` j ) ) )
  $.
$}

${
  $d D a b i j y $.

  q338886-face-box-definition $a |- (
    Q338886FaceBox D a b i
  ) = {
    y e. ( RR ^m ( D \ { i } ) ) |
      A. j e. ( D \ { i } )
        (
          ( a ` j ) <_ ( y ` j )
          /\
          ( y ` j ) <_ ( b ` j )
        )
  } $.
$}

${
  $d A D a x y i $.

  q338886-translate-definition $a |- (
    Q338886Translate D a A
  ) = {
    y e. ( RR ^m D ) |
      E. x e. A
        y = ( i e. D |-> ( ( a ` i ) + ( x ` i ) ) )
  } $.
$}

${
  $d A M $.

  q338886-measure-definition $a |- (
    Q338886Measure M A
  ) =
    ( ( toOMeas ` M ) ` A )
  $.
$}

${
  $d D i x $.

  q338886-unit-box-definition $a |- (
    Q338886UnitBox D
  ) = {
    x e. ( RR ^m D ) |
      A. i e. D
        (
          0 <_ ( x ` i )
          /\
          ( x ` i ) < 1
        )
  } $.
$}

${
  $d A D K M U a $.

  q338886-normalized-haar-definition $a |- (
    ( Q338886NormalizedHaar D M )
    <->
    (
      M e.
        (
          measures
          `
          ( sigaGen ` ( Q338886Open D ) )
        )
      /\
      A. a e. ( RR ^m D )
        A. A e. ~P ( RR ^m D )
          (
            Q338886Measure
            M
            ( Q338886Translate D a A )
          )
          =
          ( Q338886Measure M A )
      /\
      A. K e. ~P ( RR ^m D )
        (
          (
            ( ( Q338886Open D ) |`t K ) e. Comp
            ->
            ( Q338886Measure M K ) e. ( 0 [,) +oo )
          )
        )
      /\
      A. U e. ( Q338886Open D )
        (
          U =/= (/)
          ->
          0 < ( Q338886Measure M U )
        )
      /\
      (
        Q338886Measure M ( Q338886UnitBox D )
      ) = 1
    )
  ) $.
$}

${
  $d D M $.

  q338886-volume-definition $a |- (
    Q338886Volume D
  ) =
    (
      iota_ M e. U. ran measures
        ( Q338886NormalizedHaar D M )
    )
  $.
$}

${
  $d C D L W i r u v $.

  q338886-continuous-linear-definition $a |- (
    ( Q338886ContinuousLinear D W L )
    <->
    (
      L :
        ( RR ^m D )
        -->
        ( ( Base ` W ) ^m D )
      /\
      A. u e. ( RR ^m D )
        A. v e. ( RR ^m D )
          (
            L
            `
            ( i e. D |-> ( ( u ` i ) + ( v ` i ) ) )
          )
          =
          ( i e. D |->
            (
              ( ( L ` u ) ` i )
              ( +g ` W )
              ( ( L ` v ) ` i )
            )
          )
      /\
      A. r e. RR
        A. u e. ( RR ^m D )
          (
            L
            `
            ( i e. D |-> ( r x. ( u ` i ) ) )
          )
          =
          ( i e. D |->
            (
              r
              ( .s ` W )
              ( ( L ` u ) ` i )
            )
          )
      /\
      E. C e. ( 0 [,) +oo )
        A. u e. ( RR ^m D )
          (
            Q338886VecNorm D W ( L ` u )
          )
          <_
          (
            C
            x.
            ( Q338886RealNorm D u )
          )
    )
  ) $.
$}

${
  $d D F L W d e x y $.

  q338886-has-fderiv-at-definition $a |- (
    ( Q338886HasFDerivAt D W F x L )
    <->
    (
      ( Q338886ContinuousLinear D W L )
      /\
      A. e e. RR+
        E. d e. RR+
          A. y e. ( RR ^m D )
            (
              (
                Q338886RealNorm
                D
                ( Q338886RealSub D y x )
              )
              <
              d
              ->
              (
                Q338886VecNorm
                D
                W
                (
                  Q338886VecSub
                  D
                  W
                  (
                    Q338886VecSub
                    D
                    W
                    ( F ` y )
                    ( F ` x )
                  )
                  (
                    L
                    `
                    ( Q338886RealSub D y x )
                  )
                )
              )
              <_
              (
                e
                x.
                (
                  Q338886RealNorm
                  D
                  ( Q338886RealSub D y x )
                )
              )
            )
    )
  ) $.
$}

${
  $d A D F W d e x y $.

  q338886-continuous-on-definition $a |- (
    ( Q338886ContinuousOn D W F A )
    <->
    A. x e. A
      A. e e. RR+
        E. d e. RR+
          A. y e. A
            (
              (
                Q338886RealNorm
                D
                ( Q338886RealSub D y x )
              )
              <
              d
              ->
              (
                Q338886VecNorm
                D
                W
                (
                  Q338886VecSub
                  D
                  W
                  ( F ` y )
                  ( F ` x )
                )
              )
              <
              e
            )
  ) $.
$}

${
  $d D G W i x $.

  q338886-divergence-definition $a |- (
    Q338886Divergence D W G x
  ) =
    (
      W
      gsum
      ( i e. D |->
        (
          (
            ( G ` x )
            `
            ( Q338886Basis D i )
          )
          `
          i
        )
      )
    )
  $.
$}

${
  $d G M $.

  q338886-simple-definition $a |- (
    ( Q338886Simple M G )
    <->
    (
      G : U. dom M --> ( 0 [,] +oo )
      /\
      (
        G e.
          (
            dom M
            MblFnM
            (
              sigaGen
              `
              (
                TopOpen
                `
                ( RR*s |`s ( 0 [,] +oo ) )
              )
            )
          )
        /\
        ran G e. Fin
      )
    )
  ) $.
$}

${
  $d G M r $.

  q338886-simple-integral-definition $a |- (
    Q338886SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q338886-lintegral-definition $a |- (
    Q338886LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q338886Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q338886SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  $.
$}

${
  $d S W z $.

  q338886-tendsto-definition $a |- (
    ( Q338886Tendsto W S z )
    <->
    (
      S : NN0 --> ( Base ` W )
      /\
      S ( ~~>t ` ( TopOpen ` W ) ) z
    )
  ) $.
$}

${
  $d H M N S W n x $.

  q338886-aestrong-definition $a |- (
    ( Q338886AEStrong M W H )
    <->
    (
      H e. ( ( Base ` W ) ^m U. dom M )
      /\
      E. S e.
        (
          ( ( ( Base ` W ) ^m U. dom M ) )
          ^m
          NN0
        )
        (
          A. n e. NN0
            (
              ( S ` n )
                e.
                (
                  dom M
                  MblFnM
                  ( sigaGen ` ( TopOpen ` W ) )
                )
              /\
              ran ( S ` n ) e. Fin
            )
          /\
          E. N e. dom M
            (
              ( M ` N ) = 0
              /\
              A. x e. ( U. dom M \ N )
                (
                  Q338886Tendsto
                  W
                  ( n e. NN0 |-> ( ( S ` n ) ` x ) )
                  ( H ` x )
                )
            )
        )
    )
  ) $.
$}

${
  $d H M W x $.

  q338886-integrable-definition $a |- (
    ( Q338886Integrable M W H )
    <->
    (
      ( Q338886AEStrong M W H )
      /\
      (
        Q338886LIntegral
        M
        ( x e. U. dom M |->
          ( ( norm ` W ) ` ( H ` x ) )
        )
      )
      < +oo
    )
  ) $.
$}

${
  $d H K M W x $.

  q338886-diff-definition $a |- (
    Q338886Diff M W H K
  ) =
    ( x e. U. dom M |->
      (
        ( H ` x )
        ( +g ` W )
        ( ( -g ` W ) ` ( K ` x ) )
      )
    )
  $.
$}

${
  $d H K M W x $.

  q338886-l1-distance-definition $a |- (
    Q338886L1Distance M W H K
  ) =
    (
      Q338886LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q338886Diff M W H K ) ` x )
        )
      )
    )
  ) $.
$}

${
  $d H M S W n y $.

  q338886-has-integral-definition $a |- (
    ( Q338886HasIntegral M W H y )
    <->
    (
      y e. ( Base ` W )
      /\
      E. S e. ( ( ( Base ` W ) ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            ( ( S ` n ) e. dom ( W sitg M ) )
          /\
          (
            Q338886Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q338886L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q338886Tendsto
            W
            ( n e. NN0 |-> ( ( W sitg M ) ` ( S ` n ) ) )
            y
          )
        )
    )
  ) $.
$}

${
  $d A H M W x $.

  q338886-restrict-definition $a |- (
    Q338886Restrict M W A H
  ) =
    ( x e. U. dom M |->
      if
      (
        x e. A ,
        ( H ` x ) ,
        ( 0g ` W )
      )
    )
  $.
$}

${
  $d A H M W $.

  q338886-integrable-on-definition $a |- (
    ( Q338886IntegrableOn M W A H )
    <->
    (
      Q338886Integrable
      M
      W
      ( Q338886Restrict M W A H )
    )
  ) $.
$}

${
  $d H M W y $.

  q338886-total-integral-definition $a |- (
    Q338886TotalIntegral W M H
  ) =
    if
    (
      (
        W e. CMetSp
        /\
        ( Q338886Integrable M W H )
      ) ,
      (
        iota_ y e. ( Base ` W )
          ( Q338886HasIntegral M W H y )
      ) ,
      ( 0g ` W )
    )
  $.
$}

${
  $d A H M W $.

  q338886-integral-on-definition $a |- (
    Q338886IntegralOn W M A H
  ) =
    (
      Q338886TotalIntegral
      W
      M
      ( Q338886Restrict M W A H )
    )
  $.
$}

${
  $d D F W c i y $.

  q338886-face-function-definition $a |- (
    Q338886FaceFunction D W F i c
  ) =
    (
      y e. ( RR ^m ( D \ { i } ) ) |->
      (
        (
          F
          `
          ( Q338886Insert D i c y )
        )
        `
        i
      )
    )
  $.
$}

${
  $d A C D F G H K L M N S U W a b c d e i j n r u v w x y z $.

  thousand-theorems-q338886-divergence-theorem $a |-
    A. N e. NN
      A. W e.
        {
          w e. NrmVec |
          ( Scalar ` w ) = RRfld
        }
        A. a e. ( RR ^m ( 0 ..^ N ) )
          A. b e. ( RR ^m ( 0 ..^ N ) )
            A. F e.
              (
                ( ( Base ` W ) ^m ( 0 ..^ N ) )
                ^m
                ( RR ^m ( 0 ..^ N ) )
              )
              A. G e.
                (
                  (
                    (
                      ( Base ` W )
                      ^m
                      ( 0 ..^ N )
                    )
                    ^m
                    ( RR ^m ( 0 ..^ N ) )
                  )
                  ^m
                  ( RR ^m ( 0 ..^ N ) )
                )
                A. S e. ~P ( RR ^m ( 0 ..^ N ) )
                  (
                    (
                      A. i e. ( 0 ..^ N )
                        ( a ` i ) <_ ( b ` i )
                      /\
                      A. x e. ( RR ^m ( 0 ..^ N ) )
                        (
                          Q338886ContinuousLinear
                          ( 0 ..^ N )
                          W
                          ( G ` x )
                        )
                      /\
                      S ~<_ _om
                      /\
                      (
                        Q338886ContinuousOn
                        ( 0 ..^ N )
                        W
                        F
                        (
                          Q338886Box
                          ( 0 ..^ N )
                          a
                          b
                        )
                      )
                      /\
                      A. x e.
                        (
                          (
                            Q338886Interior
                            ( 0 ..^ N )
                            a
                            b
                          )
                          \
                          S
                        )
                        (
                          Q338886HasFDerivAt
                          ( 0 ..^ N )
                          W
                          F
                          x
                          ( G ` x )
                        )
                      /\
                      (
                        Q338886IntegrableOn
                        ( Q338886Volume ( 0 ..^ N ) )
                        W
                        (
                          Q338886Box
                          ( 0 ..^ N )
                          a
                          b
                        )
                        (
                          x e. ( RR ^m ( 0 ..^ N ) ) |->
                          (
                            Q338886Divergence
                            ( 0 ..^ N )
                            W
                            G
                            x
                          )
                        )
                      )
                    )
                    ->
                    (
                      Q338886IntegralOn
                      W
                      ( Q338886Volume ( 0 ..^ N ) )
                      (
                        Q338886Box
                        ( 0 ..^ N )
                        a
                        b
                      )
                      (
                        x e. ( RR ^m ( 0 ..^ N ) ) |->
                        (
                          Q338886Divergence
                          ( 0 ..^ N )
                          W
                          G
                          x
                        )
                      )
                    )
                    =
                    (
                      W
                      gsum
                      ( i e. ( 0 ..^ N ) |->
                        (
                          (
                            Q338886IntegralOn
                            W
                            (
                              Q338886Volume
                              (
                                ( 0 ..^ N )
                                \
                                { i }
                              )
                            )
                            (
                              Q338886FaceBox
                              ( 0 ..^ N )
                              a
                              b
                              i
                            )
                            (
                              Q338886FaceFunction
                              ( 0 ..^ N )
                              W
                              F
                              i
                              ( b ` i )
                            )
                          )
                          ( +g ` W )
                          (
                            ( -g ` W )
                            `
                            (
                              Q338886IntegralOn
                              W
                              (
                                Q338886Volume
                                (
                                  ( 0 ..^ N )
                                  \
                                  { i }
                                )
                              )
                              (
                                Q338886FaceBox
                                ( 0 ..^ N )
                                a
                                b
                                i
                              )
                              (
                                Q338886FaceFunction
                                ( 0 ..^ N )
                                W
                                F
                                i
                                ( a ` i )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
  $.
$}
