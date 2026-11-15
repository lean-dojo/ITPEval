$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2096184
  (thousand-theorems__metamath__Q2096184), "Plancherel theorem": the Fourier
  transform preserves the integral of the pointwise complex inner product
  for Schwartz maps from a finite-dimensional real inner-product space into
  a complex Hilbert space. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q2096184Volume is the translation-invariant Borel measure normalized so
  that the integral of exp(-pi * norm(x)^2) is one, matching mathlib's volume
  normalization on finite-dimensional real inner-product spaces.

  Q2096184Schwartz uses an orthonormal coordinate map from V to R^dim(V).
  Q2096184Jet records every iterated coordinate partial derivative as a
  continuous H-valued function. Its final clause requires every derivative
  to decay faster than every inverse polynomial. This is the standard
  coordinate characterization of an H-valued Schwartz map and is invariant
  under the internally quantified orthonormal coordinate choice.

  Q2096184Fourier is the H-valued Bochner integral of
  exp(-2*pi*i*inner(w,x)) times F(x). The vector and complex integrals are
  defined by L1-approximation with measurable finite-range functions and
  totalized by zero outside complete Bochner-integrable cases, as Lean's
  integral is. SetMM's inner product is linear in its first slot, opposite
  to mathlib's convention, so the arguments are swapped in Q2096184Pairing.

  Every declaration before the final one is syntax or a bidirectional
  definition. The final $a declaration is the single unproved corpus
  statement, and this database contains no $p proof statement.
$)

$c Q2096184Vec Q2096184Eucl Q2096184Norm Q2096184Coord
   Q2096184ONBasis Q2096184Shift Q2096184Sub Q2096184HasPartial
   Q2096184Snoc Q2096184Jet Q2096184Schwartz Q2096184Translate
   Q2096184Measure Q2096184Haar Q2096184Gaussian
   Q2096184Tendsto Q2096184AEStrong Q2096184Simple
   Q2096184SimpleIntegral Q2096184LIntegral Q2096184Diff
   Q2096184L1Distance Q2096184FunctionIntegrable
   Q2096184HasIntegral Q2096184Integral
   Q2096184NormalizedHaar Q2096184Volume Q2096184VectorIntegral
   Q2096184ComplexIntegral Q2096184Fourier Q2096184Pairing $.

q2096184-vec-syntax $a class ( Q2096184Vec V ) $.
q2096184-eucl-syntax $a class ( Q2096184Eucl V ) $.
q2096184-norm-syntax $a class ( Q2096184Norm V x ) $.
q2096184-coord-syntax $a class ( Q2096184Coord V B x ) $.
q2096184-on-basis-syntax $a wff ( Q2096184ONBasis V B ) $.
q2096184-shift-syntax $a class ( Q2096184Shift V x t i ) $.
q2096184-sub-syntax $a class ( Q2096184Sub H u v ) $.
q2096184-has-partial-syntax
  $a wff ( Q2096184HasPartial V H G i x y ) $.
q2096184-snoc-syntax $a class ( Q2096184Snoc q r i ) $.
q2096184-jet-syntax $a wff ( Q2096184Jet V H P J ) $.
q2096184-schwartz-syntax $a wff ( Q2096184Schwartz V H F ) $.
q2096184-translate-syntax $a class ( Q2096184Translate V a A ) $.
q2096184-measure-syntax $a class ( Q2096184Measure M A ) $.
q2096184-haar-syntax $a wff ( Q2096184Haar V M ) $.
q2096184-gaussian-syntax $a class ( Q2096184Gaussian V ) $.
q2096184-tendsto-syntax
  $a wff ( Q2096184Tendsto W S C ) $.
q2096184-aestrong-syntax
  $a wff ( Q2096184AEStrong M W H ) $.
q2096184-simple-syntax
  $a wff ( Q2096184Simple M G ) $.
q2096184-simple-integral-syntax
  $a class ( Q2096184SimpleIntegral M G ) $.
q2096184-lintegral-syntax
  $a class ( Q2096184LIntegral M H ) $.
q2096184-diff-syntax
  $a class ( Q2096184Diff M W H K ) $.
q2096184-l1-distance-syntax
  $a class ( Q2096184L1Distance M W H K ) $.
q2096184-function-integrable-syntax
  $a wff ( Q2096184FunctionIntegrable M W H ) $.
q2096184-has-integral-syntax
  $a wff ( Q2096184HasIntegral M W H y ) $.
q2096184-integral-syntax
  $a class ( Q2096184Integral W M H ) $.
q2096184-normalized-haar-syntax
  $a wff ( Q2096184NormalizedHaar V M ) $.
q2096184-volume-syntax $a class ( Q2096184Volume V ) $.
q2096184-vector-integral-syntax
  $a class ( Q2096184VectorIntegral V H F ) $.
q2096184-complex-integral-syntax
  $a class ( Q2096184ComplexIntegral V F ) $.
q2096184-fourier-syntax $a class ( Q2096184Fourier V H F ) $.
q2096184-pairing-syntax $a class ( Q2096184Pairing V H F G ) $.

q2096184-vec-definition $a |- (
  ( Q2096184Vec V )
  =
  ( RR ^m ( 1 ... ( dim ` V ) ) )
) $.

q2096184-eucl-definition $a |- (
  ( Q2096184Eucl V )
  =
  (
    Xt_ `
    (
      ( 1 ... ( dim ` V ) )
      X.
      { ( topGen ` ran (,) ) }
    )
  )
) $.

${
  $d V i x $.

  q2096184-norm-definition $a |- (
    ( Q2096184Norm V x )
    =
    (
      sqrt `
      (
        sum_ i e. ( 1 ... ( dim ` V ) )
          ( ( x ` i ) ^ 2 )
      )
    )
  ) $.
$}

${
  $d B V i x $.

  q2096184-coord-definition $a |- (
    ( Q2096184Coord V B x )
    =
    (
      i e. ( 1 ... ( dim ` V ) ) |->
      ( x ( .i ` V ) ( B ` i ) )
    )
  ) $.
$}

${
  $d B V i j x $.

  q2096184-on-basis-definition $a |- (
    ( Q2096184ONBasis V B )
    <->
    (
      B : ( 1 ... ( dim ` V ) ) --> ( Base ` V )
      /\
      (
        A. i e. ( 1 ... ( dim ` V ) )
          A. j e. ( 1 ... ( dim ` V ) )
            (
              ( ( B ` i ) ( .i ` V ) ( B ` j ) )
              =
              if ( i = j , 1 , 0 )
            )
        /\
        (
          x e. ( Base ` V ) |->
          ( Q2096184Coord V B x )
        )
        :
        ( Base ` V )
        -1-1-onto->
        ( Q2096184Vec V )
      )
    )
  ) $.
$}

${
  $d V i k t x $.

  q2096184-shift-definition $a |- (
    ( Q2096184Shift V x t i )
    =
    (
      k e. ( 1 ... ( dim ` V ) ) |->
      ( ( x ` k ) + if ( k = i , t , 0 ) )
    )
  ) $.
$}

${
  $d H u v $.

  q2096184-sub-definition $a |- (
    ( Q2096184Sub H u v )
    =
    ( u ( +g ` H ) ( ( -g ` H ) ` v ) )
  ) $.
$}

${
  $d G H V d e i t x y $.

  q2096184-has-partial-definition $a |- (
    ( Q2096184HasPartial V H G i x y )
    <->
    A. e e. RR+
      E. d e. RR+
        A. t e. RR
          (
            (
              0 < ( abs ` t )
              /\
              ( abs ` t ) < d
            )
            ->
            (
              ( norm ` H )
              `
              (
                Q2096184Sub
                H
                (
                  ( 1 / t )
                  ( .s ` H )
                  (
                    Q2096184Sub
                    H
                    ( G ` ( Q2096184Shift V x t i ) )
                    ( G ` x )
                  )
                )
                y
              )
            )
            < e
          )
  ) $.
$}

${
  $d i k q r $.

  q2096184-snoc-definition $a |- (
    ( Q2096184Snoc q r i )
    =
    (
      k e. ( 1 ... ( r + 1 ) ) |->
      if ( k = ( r + 1 ) , i , ( q ` k ) )
    )
  ) $.
$}

${
  $d C H J P V i n q r x $.

  q2096184-jet-definition $a |- (
    ( Q2096184Jet V H P J )
    <->
    (
      ( J ` <. 0 , (/) >. ) = P
      /\
      (
        A. r e. NN0
          A. q e.
            (
              ( 1 ... ( dim ` V ) )
              ^m
              ( 1 ... r )
            )
            (
              (
                ( J ` <. r , q >. )
                e.
                (
                  ( Base ` H )
                  ^m
                  ( Q2096184Vec V )
                )
                /\
                ( J ` <. r , q >. )
                e.
                (
                  ( Q2096184Eucl V )
                  Cn
                  ( TopOpen ` H )
                )
              )
              /\
              A. i e. ( 1 ... ( dim ` V ) )
                A. x e. ( Q2096184Vec V )
                  (
                    Q2096184HasPartial
                    V
                    H
                    ( J ` <. r , q >. )
                    i
                    x
                    (
                      ( J `
                        <.
                          ( r + 1 ) ,
                          ( Q2096184Snoc q r i )
                        >.
                      )
                      ` x
                    )
                  )
            )
        /\
        A. n e. NN0
          A. r e. NN0
            A. q e.
              (
                ( 1 ... ( dim ` V ) )
                ^m
                ( 1 ... r )
              )
              E. C e. ( 0 [,) +oo )
                A. x e. ( Q2096184Vec V )
                  (
                    (
                      ( 1 + ( Q2096184Norm V x ) )
                      ^ n
                    )
                    x.
                    (
                      ( norm ` H )
                      `
                      ( ( J ` <. r , q >. ) ` x )
                    )
                  )
                  <_ C
      )
    )
  ) $.
$}

${
  $d B F H J P V x $.

  q2096184-schwartz-definition $a |- (
    ( Q2096184Schwartz V H F )
    <->
    (
      F : ( Base ` V ) --> ( Base ` H )
      /\
      E. B E. P E. J
        (
          ( Q2096184ONBasis V B )
          /\
          (
            P : ( Q2096184Vec V ) --> ( Base ` H )
            /\
            A. x e. ( Base ` V )
              (
                ( P ` ( Q2096184Coord V B x ) )
                =
                ( F ` x )
              )
          )
          /\
          ( Q2096184Jet V H P J )
        )
    )
  ) $.
$}

${
  $d A V a x y $.

  q2096184-translate-definition $a |- (
    ( Q2096184Translate V a A )
    =
    {
      y e. ( Base ` V ) |
      E. x e. A y = ( a ( +g ` V ) x )
    }
  ) $.
$}

${
  $d A M $.

  q2096184-measure-definition $a |- (
    ( Q2096184Measure M A )
    =
    ( ( toOMeas ` M ) ` A )
  ) $.
$}

${
  $d A K M U V a $.

  q2096184-haar-definition $a |- (
    ( Q2096184Haar V M )
    <->
    (
      M e. ( measures ` ( sigaGen ` ( TopOpen ` V ) ) )
      /\
      A. a e. ( Base ` V )
        A. A e. ~P ( Base ` V )
          (
            ( Q2096184Measure M
              ( Q2096184Translate V a A ) )
            =
            ( Q2096184Measure M A )
          )
      /\
      A. K e. ~P ( Base ` V )
        (
          ( ( TopOpen ` V ) |`t K ) e. Comp
          ->
          ( Q2096184Measure M K ) e. ( 0 [,) +oo )
        )
      /\
      A. U e. ( TopOpen ` V )
        (
          U =/= (/)
          ->
          0 < ( Q2096184Measure M U )
        )
    )
  ) $.
$}

${
  $d V x $.

  q2096184-gaussian-definition $a |- (
    ( Q2096184Gaussian V )
    =
    (
      x e. ( Base ` V ) |->
      (
        exp `
        -u
        (
          _pi
          x.
          ( ( ( norm ` V ) ` x ) ^ 2 )
        )
      )
    )
  ) $.
$}

${
  $d C S W $.

  q2096184-tendsto-definition $a |- (
    ( Q2096184Tendsto W S C )
    <->
    (
      S : NN0 --> ( Base ` W )
      /\
      S ( ~~>t ` ( TopOpen ` W ) ) C
    )
  ) $.
$}

${
  $d H M N S W n x $.

  q2096184-aestrong-definition $a |- (
    ( Q2096184AEStrong M W H )
    <->
    (
      H e. ( ( Base ` W ) ^m U. dom M )
      /\
      E. S e. ( ( ( Base ` W ) ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            (
              ( S ` n )
                e. ( dom M MblFnM ( sigaGen ` ( TopOpen ` W ) ) )
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
                  Q2096184Tendsto
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
  $d G M $.

  q2096184-simple-definition $a |- (
    ( Q2096184Simple M G )
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
              sigaGen `
              ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
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

  q2096184-simple-integral-definition $a |- (
    Q2096184SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q2096184-lintegral-definition $a |- (
    Q2096184LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q2096184Simple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q2096184SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d H K M W x $.

  q2096184-diff-definition $a |- (
    Q2096184Diff M W H K
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

  q2096184-l1-distance-definition $a |- (
    Q2096184L1Distance M W H K
  ) =
    (
      Q2096184LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q2096184Diff M W H K ) ` x )
        )
      )
    )
  ) $.
$}

${
  $d H M W x $.

  q2096184-function-integrable-definition $a |- (
    ( Q2096184FunctionIntegrable M W H )
    <->
    (
      ( Q2096184AEStrong M W H )
      /\
      (
        Q2096184LIntegral
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
  $d H M S W n y $.

  q2096184-has-integral-definition $a |- (
    ( Q2096184HasIntegral M W H y )
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
            Q2096184Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q2096184L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q2096184Tendsto
            W
            ( n e. NN0 |-> ( ( W sitg M ) ` ( S ` n ) ) )
            y
          )
        )
    )
  ) $.
$}

${
  $d H M W y $.

  q2096184-integral-definition $a |- (
    Q2096184Integral W M H
  ) =
    if
    (
      (
        W e. CMetSp
        /\
        ( Q2096184FunctionIntegrable M W H )
      ) ,
      (
        iota_ y e. ( Base ` W )
          ( Q2096184HasIntegral M W H y )
      ) ,
      ( 0g ` W )
    )
  $.
$}

${
  $d M V $.

  q2096184-normalized-haar-definition $a |- (
    ( Q2096184NormalizedHaar V M )
    <->
    (
      ( Q2096184Haar V M )
      /\
      (
        Q2096184FunctionIntegrable
        M
        CCfld
        ( Q2096184Gaussian V )
      )
      /\
      (
        (
          Q2096184Integral
          CCfld
          M
          ( Q2096184Gaussian V )
        )
        =
        1
      )
    )
  ) $.
$}

${
  $d M V $.

  q2096184-volume-definition $a |- (
    ( Q2096184Volume V )
    =
    (
      iota_ M e. U. ran measures
        ( Q2096184NormalizedHaar V M )
    )
  ) $.
$}

${
  $d F H V $.

  q2096184-vector-integral-definition $a |- (
    ( Q2096184VectorIntegral V H F )
    =
    (
      Q2096184Integral
      H
      ( Q2096184Volume V )
      F
    )
  ) $.
$}

${
  $d F V $.

  q2096184-complex-integral-definition $a |- (
    ( Q2096184ComplexIntegral V F )
    =
    (
      Q2096184Integral
      CCfld
      ( Q2096184Volume V )
      F
    )
  ) $.
$}

${
  $d F H V w x $.

  q2096184-fourier-definition $a |- (
    ( Q2096184Fourier V H F )
    =
    (
      w e. ( Base ` V ) |->
      (
        Q2096184VectorIntegral
        V
        H
        (
          x e. ( Base ` V ) |->
          (
            (
              exp `
              -u
              (
                ( ( 2 x. _pi ) x. _i )
                x.
                ( w ( .i ` V ) x )
              )
            )
            ( .s ` H )
            ( F ` x )
          )
        )
      )
    )
  ) $.
$}

${
  $d F G H V x $.

  q2096184-pairing-definition $a |- (
    ( Q2096184Pairing V H F G )
    =
    (
      x e. ( Base ` V ) |->
      ( ( G ` x ) ( .i ` H ) ( F ` x ) )
    )
  ) $.
$}

${
  $d F G H V $.

  thousand-theorems-q2096184-plancherel $a |-
    A. V e.
      {
        v e. CPreHil |
        (
          ( Scalar ` v ) = RRfld
          /\
          ( dim ` v ) e. NN0
        )
      }
      A. H e.
        {
          h e. CHil |
          ( Scalar ` h ) = CCfld
        }
        A. F A. G
          (
            (
              ( Q2096184Schwartz V H F )
              /\
              ( Q2096184Schwartz V H G )
            )
            ->
            (
              Q2096184ComplexIntegral
              V
              (
                Q2096184Pairing
                V
                H
                ( Q2096184Fourier V H F )
                ( Q2096184Fourier V H G )
              )
            )
            =
            (
              Q2096184ComplexIntegral
              V
              ( Q2096184Pairing V H F G )
            )
          )
  $.
$}
