$(
  Statement-only formalization of Hundred Theorems item 047, "The Central
  Limit Theorem". This file contains no proof.
$)

$[ library/set.mm $]

$(
  The definitions below are conservative abbreviations over set.mm objects.
  P e. Prob is a probability measure, dom P is its sigma-algebra, and
  rRndVar supplies real-valued random variables.

  HT047Integral is the signed real integral obtained from the nonnegative
  simple-function integral. HT047Independent is the usual finite-event
  factorization definition of independence. HT047Law is the pushforward
  probability law on the Borel real line.

  Weak convergence is expressed through characteristic functions: the
  integrals of cos(t x) and sin(t x) converge for every real t. On Borel
  probability laws on RR this is equivalent to convergence in distribution.
  HT047StandardNormal fixes the target law by the characteristic function
  exp(-t^2/2), written as its real and imaginary parts.

  The two final assertions are respectively the zero-mean theorem in the Lean
  source and its explicitly centered form. The normalized sum contains the
  first n variables, indexed by 0 ..^ n, and n ranges over positive integers
  in the convergent law sequence. Every statement is an unproved $a
  assertion; this database contains no $p proof statements.
$)

$c HT047Simple HT047SimpleIntegral HT047NnIntegral $.
$c HT047L1 HT047Integral HT047Expectation HT047Variance $.
$c HT047SquareIntegrable HT047Law HT047RealLaw HT047Independent $.
$c HT047Normalized HT047StandardNormal HT047WeakConverges $.

ht047-simple-syntax $a wff ( HT047Simple P G ) $.
ht047-simple-integral-syntax $a class ( HT047SimpleIntegral P G ) $.
ht047-nn-integral-syntax $a class ( HT047NnIntegral P H ) $.
ht047-l1-syntax $a class ( HT047L1 P ) $.
ht047-integral-syntax $a class ( HT047Integral P ) $.
ht047-expectation-syntax $a class ( HT047Expectation P H ) $.
ht047-variance-syntax $a class ( HT047Variance P H ) $.
ht047-square-integrable-syntax $a wff ( HT047SquareIntegrable P H ) $.
ht047-law-syntax $a class ( HT047Law P H ) $.
ht047-real-law-syntax $a wff ( HT047RealLaw M ) $.
ht047-independent-syntax $a wff ( HT047Independent P X ) $.
ht047-normalized-syntax $a class ( HT047Normalized P X M S N ) $.
ht047-standard-normal-syntax $a wff ( HT047StandardNormal M ) $.
ht047-weak-converges-syntax $a wff ( HT047WeakConverges L M ) $.

${
  $d G P x $.

  ht047-simple-definition $a |- (
    ( HT047Simple P G )
    <->
    (
      G e. ( dom P MblFnM BrSiga )
      /\
      (
        G : U. dom P --> RR
        /\
        (
          ran G e. Fin
          /\
          A. x e. U. dom P 0 <_ ( G ` x )
        )
      )
    )
  ) $.
$}

${
  $d G P y $.

  ht047-simple-integral-definition $a |- (
    HT047SimpleIntegral P G
    =
    sum_ y e. ( ran G \ { 0 } )
      ( y x. ( P ` ( `' G " { y } ) ) )
  ) $.
$}

${
  $d H P g r x $.

  ht047-nn-integral-definition $a |- (
    HT047NnIntegral P H
    =
    sup
    (
      { r e. RR |
        E. g
          (
            ( HT047Simple P g )
            /\
            (
              A. x e. U. dom P ( g ` x ) <_ ( H ` x )
              /\
              r = ( HT047SimpleIntegral P g )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d P h x $.

  ht047-l1-definition $a |- (
    HT047L1 P
    =
    { h e. ( rRndVar ` P ) |
      ( HT047NnIntegral P
        ( x e. U. dom P |-> ( abs ` ( h ` x ) ) )
      ) e. RR
    }
  ) $.
$}

${
  $d H P x $.

  ht047-integral-definition $a |- (
    HT047Integral P
    =
    ( H e. ( HT047L1 P ) |->
      (
        ( HT047NnIntegral P
          ( x e. U. dom P |->
            if ( 0 <_ ( H ` x ) , ( H ` x ) , 0 ) )
        )
        -
        ( HT047NnIntegral P
          ( x e. U. dom P |->
            if ( ( H ` x ) < 0 , -u ( H ` x ) , 0 ) )
        )
      )
    )
  ) $.
$}

ht047-expectation-definition $a |- (
  HT047Expectation P H
  =
  ( ( HT047Integral P ) ` H )
) $.

${
  $d H P x $.

  ht047-variance-definition $a |- (
    HT047Variance P H
    =
    (
      ( HT047Integral P )
      `
      ( x e. U. dom P |->
        ( ( ( H ` x ) - ( HT047Expectation P H ) ) ^ 2 )
      )
    )
  ) $.
$}

${
  $d H P x $.

  ht047-square-integrable-definition $a |- (
    ( HT047SquareIntegrable P H )
    <->
    (
      H e. ( HT047L1 P )
      /\
      ( x e. U. dom P |-> ( ( H ` x ) ^ 2 ) )
        e. ( HT047L1 P )
    )
  ) $.
$}

${
  $d H P a $.

  ht047-law-definition $a |- (
    HT047Law P H
    =
    ( a e. BrSiga |-> ( P ` ( `' H " a ) ) )
  ) $.
$}

ht047-real-law-definition $a |- (
  ( HT047RealLaw M )
  <->
  ( M e. Prob /\ dom M = BrSiga )
) $.

${
  $d P X b i s $.

  ht047-independent-definition $a |- (
    ( HT047Independent P X )
    <->
    (
      X : NN0 --> ( rRndVar ` P )
      /\
      A. s e. Fin
        (
          ( s C_ NN0 /\ s =/= (/) )
          ->
          A. b
            (
              b : s --> BrSiga
              ->
              (
                P
                `
                |^|_ i e. s
                  ( `' ( X ` i ) " ( b ` i ) )
              )
              =
              prod_ i e. s
                ( P ` ( `' ( X ` i ) " ( b ` i ) ) )
            )
        )
    )
  ) $.
$}

${
  $d M N P S X i x $.

  ht047-normalized-definition $a |- (
    HT047Normalized P X M S N
    =
    ( x e. U. dom P |->
      (
        sum_ i e. ( 0 ..^ N )
          ( ( ( X ` i ) ` x ) - M )
      )
      /
      ( sqrt ` ( N x. ( S ^ 2 ) ) )
    )
  ) $.
$}

${
  $d M t x $.

  ht047-standard-normal-definition $a |- (
    ( HT047StandardNormal M )
    <->
    (
      ( HT047RealLaw M )
      /\
      A. t e. RR
        (
          (
            ( HT047Integral M )
            `
            ( x e. RR |-> ( cos ` ( t x. x ) ) )
          )
          =
          ( exp ` ( -u ( ( t ^ 2 ) / 2 ) ) )
          /\
          (
            ( HT047Integral M )
            `
            ( x e. RR |-> ( sin ` ( t x. x ) ) )
          )
          =
          0
        )
    )
  ) $.
$}

${
  $d L M e k n q t x $.

  ht047-weak-converges-definition $a |- (
    ( HT047WeakConverges L M )
    <->
    (
      (
        L : NN --> { q e. Prob | dom q = BrSiga }
        /\
        ( HT047RealLaw M )
      )
      /\
      A. t e. RR A. e e. RR+
        E. k e. NN A. n e. ( ZZ>= ` k )
          (
            (
              abs
              `
              (
                (
                  ( HT047Integral ( L ` n ) )
                  `
                  ( x e. RR |-> ( cos ` ( t x. x ) ) )
                )
                -
                (
                  ( HT047Integral M )
                  `
                  ( x e. RR |-> ( cos ` ( t x. x ) ) )
                )
              )
            )
            <
            e
            /\
            (
              abs
              `
              (
                (
                  ( HT047Integral ( L ` n ) )
                  `
                  ( x e. RR |-> ( sin ` ( t x. x ) ) )
                )
                -
                (
                  ( HT047Integral M )
                  `
                  ( x e. RR |-> ( sin ` ( t x. x ) ) )
                )
              )
            )
            <
            e
          )
    )
  ) $.
$}

${
  $d D P R X i n u $.

  hundred-theorems-047-central-limit-theorem-zero-mean $a |- (
    (
      (
        P e. Prob
        /\
        ( HT047RealLaw D )
      )
      /\
      (
        ( HT047Independent P X )
        /\
        (
          A. i e. NN0 ( HT047Expectation P ( X ` i ) ) = 0
          /\
          (
            0 < R
            /\
            (
              A. i e. NN0
                ( HT047SquareIntegrable P ( X ` i ) )
              /\
              (
                A. i e. NN0
                  ( HT047Variance P ( X ` i ) ) = ( R ^ 2 )
                /\
                A. i e. NN0
                  ( HT047Law P ( X ` i ) ) = D
              )
            )
          )
        )
      )
    )
    ->
    E. u
      (
        ( HT047StandardNormal u )
        /\
        (
          HT047WeakConverges
          ( n e. NN |->
            ( HT047Law P
              ( HT047Normalized P X 0 R n )
            )
          )
          u
        )
      )
  ) $.
$}

${
  $d D M P R X i n u $.

  hundred-theorems-047-central-limit-theorem $a |- (
    (
      (
        (
          P e. Prob
          /\
          ( HT047RealLaw D )
        )
        /\
        M e. RR
      )
      /\
      (
        ( HT047Independent P X )
        /\
        (
          A. i e. NN0 ( HT047Expectation P ( X ` i ) ) = M
          /\
          (
            0 < R
            /\
            (
              A. i e. NN0
                ( HT047SquareIntegrable P ( X ` i ) )
              /\
              (
                A. i e. NN0
                  ( HT047Variance P ( X ` i ) ) = ( R ^ 2 )
                /\
                A. i e. NN0
                  ( HT047Law P ( X ` i ) ) = D
              )
            )
          )
        )
      )
    )
    ->
    E. u
      (
        ( HT047StandardNormal u )
        /\
        (
          HT047WeakConverges
          ( n e. NN |->
            ( HT047Law P
              ( HT047Normalized P X M R n )
            )
          )
          u
        )
      )
  ) $.
$}
