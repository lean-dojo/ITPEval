$(
  Statement-only formalization of Thousand Theorems corpus artifact Q179467
  (thousand-theorems__metamath__Q179467), "Fourier theorem": for an
  integrable function from a finite-dimensional real inner-product space to
  a complex Banach space whose Fourier transform is integrable, inverse
  Fourier transformation recovers the function at each continuity point;
  for a continuous function it recovers the whole function. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q179467Volume is the translation-invariant Borel measure normalized so
  that the integral of exp(-pi * norm(x)^2) is one, matching mathlib's volume
  normalization on finite-dimensional real inner-product spaces.

  Q179467FunctionIntegrable encodes almost-everywhere strong measurability
  and finite L1 norm. Q179467Integral is the totalized Banach-valued Bochner
  integral defined by L1 limits of measurable finite-range functions.
  Q179467Fourier and Q179467FourierInv are the Banach-valued Bochner Fourier
  transform and inverse Fourier transform with kernels
  exp(-2*pi*i*inner(w,x)) and exp(2*pi*i*inner(w,x)), respectively.
  Q179467ContinuousAt is the usual open-set definition of continuity at a
  point.

  Every declaration before the final one is syntax or a bidirectional
  definition. The final $a declaration directly packages the two indexed
  unproved statements. The root artifact contains no $p declaration; the
  included lib/set.mm supplies the proved standard library.
$)

$c Q179467Translate Q179467Measure Q179467Haar
   Q179467Gaussian Q179467Tendsto Q179467AEStrong
   Q179467Simple Q179467SimpleIntegral Q179467LIntegral
   Q179467Diff Q179467L1Distance Q179467FunctionIntegrable
   Q179467HasIntegral Q179467Integral
   Q179467NormalizedHaar Q179467Volume
   Q179467ContinuousAt Q179467Fourier Q179467FourierInv $.

q179467-translate-syntax $a class ( Q179467Translate V a A ) $.
q179467-measure-syntax $a class ( Q179467Measure M A ) $.
q179467-haar-syntax $a wff ( Q179467Haar V M ) $.
q179467-gaussian-syntax $a class ( Q179467Gaussian V ) $.
q179467-tendsto-syntax
  $a wff ( Q179467Tendsto W S C ) $.
q179467-aestrong-syntax
  $a wff ( Q179467AEStrong M W H ) $.
q179467-simple-syntax
  $a wff ( Q179467Simple M G ) $.
q179467-simple-integral-syntax
  $a class ( Q179467SimpleIntegral M G ) $.
q179467-lintegral-syntax
  $a class ( Q179467LIntegral M H ) $.
q179467-diff-syntax
  $a class ( Q179467Diff M W H K ) $.
q179467-l1-distance-syntax
  $a class ( Q179467L1Distance M W H K ) $.
q179467-function-integrable-syntax
  $a wff ( Q179467FunctionIntegrable M W H ) $.
q179467-has-integral-syntax
  $a wff ( Q179467HasIntegral M W H y ) $.
q179467-integral-syntax
  $a class ( Q179467Integral W M H ) $.
q179467-normalized-haar-syntax
  $a wff ( Q179467NormalizedHaar V M ) $.
q179467-volume-syntax $a class ( Q179467Volume V ) $.
q179467-continuous-at-syntax
  $a wff ( Q179467ContinuousAt V E F z ) $.
q179467-fourier-syntax $a class ( Q179467Fourier V E F ) $.
q179467-fourier-inv-syntax $a class ( Q179467FourierInv V E F ) $.

${
  $d A V a x y $.

  q179467-translate-definition $a |- (
    ( Q179467Translate V a A )
    =
    {
      y e. ( Base ` V ) |
      E. x e. A y = ( a ( +g ` V ) x )
    }
  ) $.
$}

${
  $d A M $.

  q179467-measure-definition $a |- (
    ( Q179467Measure M A )
    =
    ( ( toOMeas ` M ) ` A )
  ) $.
$}

${
  $d A K M U V a $.

  q179467-haar-definition $a |- (
    ( Q179467Haar V M )
    <->
    (
      M e. ( measures ` ( sigaGen ` ( TopOpen ` V ) ) )
      /\
      A. a e. ( Base ` V )
        A. A e. ~P ( Base ` V )
          (
            ( Q179467Measure M ( Q179467Translate V a A ) )
            =
            ( Q179467Measure M A )
          )
      /\
      A. K e. ~P ( Base ` V )
        (
          ( ( TopOpen ` V ) |`t K ) e. Comp
          ->
          ( Q179467Measure M K ) e. ( 0 [,) +oo )
        )
      /\
      A. U e. ( TopOpen ` V )
        (
          U =/= (/)
          ->
          0 < ( Q179467Measure M U )
        )
    )
  ) $.
$}

${
  $d V x $.

  q179467-gaussian-definition $a |- (
    ( Q179467Gaussian V )
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

  q179467-tendsto-definition $a |- (
    ( Q179467Tendsto W S C )
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

  q179467-aestrong-definition $a |- (
    ( Q179467AEStrong M W H )
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
                  Q179467Tendsto
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

  q179467-simple-definition $a |- (
    ( Q179467Simple M G )
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

  q179467-simple-integral-definition $a |- (
    Q179467SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q179467-lintegral-definition $a |- (
    Q179467LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q179467Simple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q179467SimpleIntegral M G )
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

  q179467-diff-definition $a |- (
    Q179467Diff M W H K
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

  q179467-l1-distance-definition $a |- (
    Q179467L1Distance M W H K
  ) =
    (
      Q179467LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q179467Diff M W H K ) ` x )
        )
      )
    )
  ) $.
$}

${
  $d H M W x $.

  q179467-function-integrable-definition $a |- (
    ( Q179467FunctionIntegrable M W H )
    <->
    (
      ( Q179467AEStrong M W H )
      /\
      (
        Q179467LIntegral
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

  q179467-has-integral-definition $a |- (
    ( Q179467HasIntegral M W H y )
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
            Q179467Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q179467L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q179467Tendsto
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

  q179467-integral-definition $a |- (
    Q179467Integral W M H
  ) =
    if
    (
      (
        W e. CMetSp
        /\
        ( Q179467FunctionIntegrable M W H )
      ) ,
      (
        iota_ y e. ( Base ` W )
          ( Q179467HasIntegral M W H y )
      ) ,
      ( 0g ` W )
    )
  $.
$}

${
  $d M V $.

  q179467-normalized-haar-definition $a |- (
    ( Q179467NormalizedHaar V M )
    <->
    (
      ( Q179467Haar V M )
      /\
      (
        Q179467FunctionIntegrable
        M
        CCfld
        ( Q179467Gaussian V )
      )
      /\
      (
        (
          Q179467Integral
          CCfld
          M
          ( Q179467Gaussian V )
        )
        =
        1
      )
    )
  ) $.
$}

${
  $d M V $.

  q179467-volume-definition $a |- (
    ( Q179467Volume V )
    =
    (
      iota_ M e. U. ran measures
        ( Q179467NormalizedHaar V M )
    )
  ) $.
$}

${
  $d E F O U V x z $.

  q179467-continuous-at-definition $a |- (
    ( Q179467ContinuousAt V E F z )
    <->
    A. O e. ( TopOpen ` E )
      (
        ( F ` z ) e. O
        ->
        E. U e. ( TopOpen ` V )
          (
            z e. U
            /\
            A. x e. U ( F ` x ) e. O
          )
      )
  ) $.
$}

${
  $d E F V w x $.

  q179467-fourier-definition $a |- (
    ( Q179467Fourier V E F )
    =
    (
      w e. ( Base ` V ) |->
      (
        Q179467Integral
        E
        ( Q179467Volume V )
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

  q179467-fourier-inv-definition $a |- (
    ( Q179467FourierInv V E F )
    =
    (
      x e. ( Base ` V ) |->
      (
        Q179467Integral
        E
        ( Q179467Volume V )
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
  $d E F V z $.

  thousand-theorems-q179467-fourier-theorem $a |-
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
            A. z e. ( Base ` V )
              (
                (
                  (
                    (
                      Q179467FunctionIntegrable
                      ( Q179467Volume V )
                      E
                      F
                    )
                    /\
                    (
                      Q179467FunctionIntegrable
                      ( Q179467Volume V )
                      E
                      ( Q179467Fourier V E F )
                      )
                  )
                  /\
                  ( Q179467ContinuousAt V E F z )
                )
                ->
                (
                  (
                    Q179467FourierInv
                    V
                    E
                    ( Q179467Fourier V E F )
                  )
                  ` z
                )
                =
                ( F ` z )
              )
            /\
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
                    Q179467FunctionIntegrable
                    ( Q179467Volume V )
                    E
                    F
                    )
                )
                /\
                (
                  Q179467FunctionIntegrable
                  ( Q179467Volume V )
                  E
                  ( Q179467Fourier V E F )
                  )
              )
              ->
              (
                Q179467FourierInv
                V
                E
                ( Q179467Fourier V E F )
              )
              =
              F
            )
          )
  $.
$}
