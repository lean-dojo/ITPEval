$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3984053
  (thousand-theorems__metamath__Q3984053), "Fourier inversion theorem":
  for a continuous integrable function from a finite-dimensional real
  inner-product space to a complex Banach space, if its Fourier transform is
  integrable, then applying the inverse Fourier transform recovers the
  original function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q3984053Volume is the translation-invariant Borel measure normalized so
  that the integral of exp(-pi * norm(x)^2) is one, matching mathlib's volume
  normalization on finite-dimensional real inner-product spaces.

  Q3984053FunctionIntegrable encodes almost-everywhere strong measurability
  and finite L1 norm. Q3984053Integral is the totalized Banach-valued
  Bochner integral defined by L1 limits of measurable finite-range functions.
  Q3984053Fourier and Q3984053FourierInv are the Bochner Fourier transform
  and inverse Fourier transform with kernels exp(-2*pi*i*inner(w,x)) and
  exp(2*pi*i*inner(w,x)), respectively.

  Every declaration before the final one is syntax or a bidirectional
  definition. The final $a declaration is the single unproved corpus
  statement, and this database contains no $p proof statement.
$)

$c Q3984053Translate Q3984053Measure Q3984053Haar
   Q3984053Gaussian Q3984053Tendsto Q3984053AEStrong
   Q3984053Simple Q3984053SimpleIntegral Q3984053LIntegral
   Q3984053Diff Q3984053L1Distance Q3984053FunctionIntegrable
   Q3984053HasIntegral Q3984053Integral
   Q3984053NormalizedHaar Q3984053Volume
   Q3984053Fourier Q3984053FourierInv $.

q3984053-translate-syntax $a class ( Q3984053Translate V a A ) $.
q3984053-measure-syntax $a class ( Q3984053Measure M A ) $.
q3984053-haar-syntax $a wff ( Q3984053Haar V M ) $.
q3984053-gaussian-syntax $a class ( Q3984053Gaussian V ) $.
q3984053-tendsto-syntax
  $a wff ( Q3984053Tendsto W S C ) $.
q3984053-aestrong-syntax
  $a wff ( Q3984053AEStrong M W H ) $.
q3984053-simple-syntax
  $a wff ( Q3984053Simple M G ) $.
q3984053-simple-integral-syntax
  $a class ( Q3984053SimpleIntegral M G ) $.
q3984053-lintegral-syntax
  $a class ( Q3984053LIntegral M H ) $.
q3984053-diff-syntax
  $a class ( Q3984053Diff M W H K ) $.
q3984053-l1-distance-syntax
  $a class ( Q3984053L1Distance M W H K ) $.
q3984053-function-integrable-syntax
  $a wff ( Q3984053FunctionIntegrable M W H ) $.
q3984053-has-integral-syntax
  $a wff ( Q3984053HasIntegral M W H y ) $.
q3984053-integral-syntax
  $a class ( Q3984053Integral W M H ) $.
q3984053-normalized-haar-syntax
  $a wff ( Q3984053NormalizedHaar V M ) $.
q3984053-volume-syntax $a class ( Q3984053Volume V ) $.
q3984053-fourier-syntax $a class ( Q3984053Fourier V E F ) $.
q3984053-fourier-inv-syntax $a class ( Q3984053FourierInv V E F ) $.

${
  $d A V a x y $.

  q3984053-translate-definition $a |- (
    ( Q3984053Translate V a A )
    =
    {
      y e. ( Base ` V ) |
      E. x e. A y = ( a ( +g ` V ) x )
    }
  ) $.
$}

${
  $d A M $.

  q3984053-measure-definition $a |- (
    ( Q3984053Measure M A )
    =
    ( ( toOMeas ` M ) ` A )
  ) $.
$}

${
  $d A K M U V a $.

  q3984053-haar-definition $a |- (
    ( Q3984053Haar V M )
    <->
    (
      M e. ( measures ` ( sigaGen ` ( TopOpen ` V ) ) )
      /\
      A. a e. ( Base ` V )
        A. A e. ~P ( Base ` V )
          (
            ( Q3984053Measure M ( Q3984053Translate V a A ) )
            =
            ( Q3984053Measure M A )
          )
      /\
      A. K e. ~P ( Base ` V )
        (
          ( ( TopOpen ` V ) |`t K ) e. Comp
          ->
          ( Q3984053Measure M K ) e. ( 0 [,) +oo )
        )
      /\
      A. U e. ( TopOpen ` V )
        (
          U =/= (/)
          ->
          0 < ( Q3984053Measure M U )
        )
    )
  ) $.
$}

${
  $d V x $.

  q3984053-gaussian-definition $a |- (
    ( Q3984053Gaussian V )
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

  q3984053-tendsto-definition $a |- (
    ( Q3984053Tendsto W S C )
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

  q3984053-aestrong-definition $a |- (
    ( Q3984053AEStrong M W H )
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
                  Q3984053Tendsto
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

  q3984053-simple-definition $a |- (
    ( Q3984053Simple M G )
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

  q3984053-simple-integral-definition $a |- (
    Q3984053SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q3984053-lintegral-definition $a |- (
    Q3984053LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q3984053Simple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q3984053SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  $.
$}

${
  $d H K M W x $.

  q3984053-diff-definition $a |- (
    Q3984053Diff M W H K
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

  q3984053-l1-distance-definition $a |- (
    Q3984053L1Distance M W H K
  ) =
    (
      Q3984053LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q3984053Diff M W H K ) ` x )
        )
      )
    )
  ) $.
$}

${
  $d H M W x $.

  q3984053-function-integrable-definition $a |- (
    ( Q3984053FunctionIntegrable M W H )
    <->
    (
      ( Q3984053AEStrong M W H )
      /\
      (
        Q3984053LIntegral
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

  q3984053-has-integral-definition $a |- (
    ( Q3984053HasIntegral M W H y )
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
            Q3984053Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q3984053L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q3984053Tendsto
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

  q3984053-integral-definition $a |- (
    Q3984053Integral W M H
  ) =
    if
    (
      (
        W e. CMetSp
        /\
        ( Q3984053FunctionIntegrable M W H )
      ) ,
      (
        iota_ y e. ( Base ` W )
          ( Q3984053HasIntegral M W H y )
      ) ,
      ( 0g ` W )
    )
  $.
$}

${
  $d M V $.

  q3984053-normalized-haar-definition $a |- (
    ( Q3984053NormalizedHaar V M )
    <->
    (
      ( Q3984053Haar V M )
      /\
      (
        Q3984053FunctionIntegrable
        M
        CCfld
        ( Q3984053Gaussian V )
      )
      /\
      (
        (
          Q3984053Integral
          CCfld
          M
          ( Q3984053Gaussian V )
        )
        =
        1
      )
    )
  ) $.
$}

${
  $d M V $.

  q3984053-volume-definition $a |- (
    ( Q3984053Volume V )
    =
    (
      iota_ M e. U. ran measures
        ( Q3984053NormalizedHaar V M )
    )
  ) $.
$}

${
  $d E F V w x $.

  q3984053-fourier-definition $a |- (
    ( Q3984053Fourier V E F )
    =
    (
      w e. ( Base ` V ) |->
      (
        Q3984053Integral
        E
        ( Q3984053Volume V )
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
            ( .s ` E )
            ( F ` x )
          )
        )
      )
    )
  ) $.
$}

${
  $d E F V w x $.

  q3984053-fourier-inv-definition $a |- (
    ( Q3984053FourierInv V E F )
    =
    (
      x e. ( Base ` V ) |->
      (
        Q3984053Integral
        E
        ( Q3984053Volume V )
        (
          w e. ( Base ` V ) |->
          (
            (
              exp `
              (
                ( ( 2 x. _pi ) x. _i )
                x.
                ( w ( .i ` V ) x )
              )
            )
            ( .s ` E )
            ( F ` w )
          )
        )
      )
    )
  ) $.
$}

${
  $d E F V $.

  thousand-theorems-q3984053-fourier-inversion $a |-
    A. V e.
      {
        v e. CPreHil |
        (
          ( Scalar ` v ) = RRfld
          /\
          ( dim ` v ) e. NN0
        )
      }
      A. E e.
        {
          e e. Ban |
          ( Scalar ` e ) = CCfld
        }
        A. F e. ( ( Base ` E ) ^m ( Base ` V ) )
          (
            (
              (
                F e.
                  (
                    ( TopOpen ` V )
                    Cn
                    ( TopOpen ` E )
                  )
                /\
                (
                  Q3984053FunctionIntegrable
                  ( Q3984053Volume V )
                  E
                  F
                )
              )
              /\
              (
                Q3984053FunctionIntegrable
                ( Q3984053Volume V )
                E
                ( Q3984053Fourier V E F )
              )
            )
            ->
            (
              Q3984053FourierInv
              V
              E
              ( Q3984053Fourier V E F )
            )
            =
            F
          )
  $.
$}
