$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1443036
  (thousand-theorems__metamath__Q1443036), "Parseval's theorem": for every
  complex square-integrable function on a positive-period additive circle,
  the sum over all integer Fourier modes of the squared coefficient norms
  equals the normalized integral of the squared function norm. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1443036Circle T is the canonical half-open representative interval
  [0,T) for AddCircle T = RR / T*ZZ. Its normalized Lebesgue measure
  (1/T) vol is exactly the probability Haar measure haarAddCircle.
  Changing the representative at the omitted endpoint is measure-null.

  Q1443036Restrict zero-extends a circle representative to RR.
  Q1443036L2 says that the complex representative and its squared modulus
  are Lebesgue integrable. Q1443036FunctionIntegrable encodes
  almost-everywhere strong measurability and finite L1 norm, while
  Q1443036TotalIntegral is the corresponding totalized Bochner integral
  defined by L1 limits of measurable finite-range functions. On the finite
  interval [0,T), Q1443036L2 is bidirectionally equivalent to strong
  measurability and membership in the source Lp CC 2 haarAddCircle space.

  Q1443036FourierCoeff is the normalized integral of
  exp(-2*pi*i*n*x/T) F(x). Q1443036Series is the supremum of all finite
  subsums of the nonnegative family |FourierCoeff(n)|^2; this is the
  nonnegative-series form of the source integer-indexed tsum.

  Every declaration before the final one is syntax or a transparent
  definition. The final $a declaration is the unproved corpus statement;
  this database contains no $p proof statement.
$)

$c Q1443036Circle Q1443036Restrict Q1443036Tendsto Q1443036AEStrong
   Q1443036Simple Q1443036SimpleIntegral Q1443036LIntegral
   Q1443036Diff Q1443036L1Distance Q1443036FunctionIntegrable
   Q1443036HasIntegral Q1443036TotalIntegral Q1443036EnergyIntegrand
   Q1443036L2 Q1443036FourierIntegrand Q1443036FourierCoeff
   Q1443036CoeffSquare Q1443036Energy Q1443036Series $.

q1443036-circle-syntax
  $a class ( Q1443036Circle T ) $.
q1443036-restrict-syntax
  $a class ( Q1443036Restrict T F ) $.
q1443036-tendsto-syntax
  $a wff ( Q1443036Tendsto W S C ) $.
q1443036-aestrong-syntax
  $a wff ( Q1443036AEStrong M W H ) $.
q1443036-simple-syntax
  $a wff ( Q1443036Simple M G ) $.
q1443036-simple-integral-syntax
  $a class ( Q1443036SimpleIntegral M G ) $.
q1443036-lintegral-syntax
  $a class ( Q1443036LIntegral M H ) $.
q1443036-diff-syntax
  $a class ( Q1443036Diff M W H K ) $.
q1443036-l1-distance-syntax
  $a class ( Q1443036L1Distance M W H K ) $.
q1443036-function-integrable-syntax
  $a wff ( Q1443036FunctionIntegrable M W H ) $.
q1443036-has-integral-syntax
  $a wff ( Q1443036HasIntegral M W H y ) $.
q1443036-total-integral-syntax
  $a class ( Q1443036TotalIntegral W H ) $.
q1443036-energy-integrand-syntax
  $a class ( Q1443036EnergyIntegrand T F ) $.
q1443036-l2-syntax
  $a wff ( Q1443036L2 T F ) $.
q1443036-fourier-integrand-syntax
  $a class ( Q1443036FourierIntegrand T F n ) $.
q1443036-fourier-coeff-syntax
  $a class ( Q1443036FourierCoeff T F n ) $.
q1443036-coeff-square-syntax
  $a class ( Q1443036CoeffSquare T F n ) $.
q1443036-energy-syntax
  $a class ( Q1443036Energy T F ) $.
q1443036-series-syntax
  $a class ( Q1443036Series T F ) $.

${
  q1443036-circle-definition $a |- (
    Q1443036Circle T
  ) = ( 0 [,) T ) $.
$}

${
  $d F T x $.

  q1443036-restrict-definition $a |- (
    Q1443036Restrict T F
  ) = (
    x e. RR |->
    if (
      x e. ( Q1443036Circle T ) ,
      ( F ` x ) ,
      0
    )
  ) $.
$}

${
  $d C S W $.

  q1443036-tendsto-definition $a |- (
    ( Q1443036Tendsto W S C )
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

  q1443036-aestrong-definition $a |- (
    ( Q1443036AEStrong M W H )
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
                  Q1443036Tendsto
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

  q1443036-simple-definition $a |- (
    ( Q1443036Simple M G )
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

  q1443036-simple-integral-definition $a |- (
    Q1443036SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q1443036-lintegral-definition $a |- (
    Q1443036LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q1443036Simple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q1443036SimpleIntegral M G )
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

  q1443036-diff-definition $a |- (
    Q1443036Diff M W H K
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

  q1443036-l1-distance-definition $a |- (
    Q1443036L1Distance M W H K
  ) =
    (
      Q1443036LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q1443036Diff M W H K ) ` x )
        )
      )
    )
  ) $.
$}

${
  $d H M W x $.

  q1443036-function-integrable-definition $a |- (
    ( Q1443036FunctionIntegrable M W H )
    <->
    (
      ( Q1443036AEStrong M W H )
      /\
      (
        Q1443036LIntegral
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

  q1443036-has-integral-definition $a |- (
    ( Q1443036HasIntegral M W H y )
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
            Q1443036Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q1443036L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q1443036Tendsto
            W
            ( n e. NN0 |-> ( ( W sitg M ) ` ( S ` n ) ) )
            y
          )
        )
    )
  ) $.
$}

${
  $d H W y $.

  q1443036-total-integral-definition $a |- (
    Q1443036TotalIntegral W H
  ) =
    if
    (
      (
        W e. CMetSp
        /\
        ( Q1443036FunctionIntegrable vol W H )
      ) ,
      (
        iota_ y e. ( Base ` W )
          ( Q1443036HasIntegral vol W H y )
      ) ,
      ( 0g ` W )
    )
  $.
$}

${
  $d F T x $.

  q1443036-energy-integrand-definition $a |- (
    Q1443036EnergyIntegrand T F
  ) = (
    x e. RR |->
    if (
      x e. ( Q1443036Circle T ) ,
      ( ( abs ` ( F ` x ) ) ^ 2 ) ,
      0
    )
  ) $.
$}

${
  $d F T $.

  q1443036-l2-definition $a |- (
    ( Q1443036L2 T F )
    <->
    (
      F e. ( CC ^m ( Q1443036Circle T ) )
      /\
      (
        Q1443036FunctionIntegrable
        vol
        CCfld
        ( Q1443036Restrict T F )
      )
      /\
      (
        Q1443036FunctionIntegrable
        vol
        RRfld
        ( Q1443036EnergyIntegrand T F )
      )
    )
  ) $.
$}

${
  $d F T n x $.

  q1443036-fourier-integrand-definition $a |- (
    Q1443036FourierIntegrand T F n
  ) = (
    x e. RR |->
    if (
      x e. ( Q1443036Circle T ) ,
      (
        (
          exp `
          -u
          (
            (
              (
                ( ( 2 x. _pi ) x. _i )
                x.
                n
              )
              x.
              x
            )
            /
            T
          )
        )
        x.
        ( F ` x )
      ) ,
      0
    )
  ) $.
$}

${
  $d F T n $.

  q1443036-fourier-coeff-definition $a |- (
    Q1443036FourierCoeff T F n
  ) = (
    ( 1 / T )
    x.
    (
      Q1443036TotalIntegral
      CCfld
      ( Q1443036FourierIntegrand T F n )
    )
  ) $.
$}

${
  $d F T n $.

  q1443036-coeff-square-definition $a |- (
    Q1443036CoeffSquare T F n
  ) = (
    (
      abs `
      ( Q1443036FourierCoeff T F n )
    )
    ^
    2
  ) $.
$}

${
  $d F T $.

  q1443036-energy-definition $a |- (
    Q1443036Energy T F
  ) = (
    ( 1 / T )
    x.
    (
      Q1443036TotalIntegral
      RRfld
      ( Q1443036EnergyIntegrand T F )
    )
  ) $.
$}

${
  $d A F T n $.

  q1443036-series-definition $a |- (
    Q1443036Series T F
  ) = sup (
    ran (
      A e. ( ~P ZZ i^i Fin ) |->
      (
        sum_ n e. A
          ( Q1443036CoeffSquare T F n )
      )
    ) ,
    RR ,
    <
  ) $.
$}

${
  $d F T $.

  thousand-theorems-q1443036-parseval-s-theorem $a |-
    A. T e. RR+
      A. F e. ( CC ^m ( Q1443036Circle T ) )
        (
          ( Q1443036L2 T F )
          ->
          (
            ( Q1443036Series T F )
            =
            ( Q1443036Energy T F )
          )
        )
  $.
$}
