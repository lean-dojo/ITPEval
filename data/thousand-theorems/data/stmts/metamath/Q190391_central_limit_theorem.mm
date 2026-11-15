$(
  Statement-only formalization of Thousand Theorems corpus artifact Q190391
  (thousand-theorems__metamath__Q190391), "Central limit theorem":
  independent identically distributed real random variables with a finite
  second moment have centered inverse-square-root normalized partial sums
  converging in distribution to the zero-mean Gaussian law with their
  variance. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  M and N range over arbitrary SetMM probability measures, so their sample
  spaces and sigma-algebras remain arbitrary. Q190391AERep records a Borel
  measurable representative equal to a real-valued function off a measurable
  null set. Q190391Map is the resulting pushforward probability measure.

  Q190391MemLpTwo is the real L^2 condition: a measurable representative has
  integrable square. Over a probability measure this is equivalent to Lean's
  MemLp at exponent 2. Q190391Mean and Q190391Variance use the unique
  representative-independent real integral and centered-square integral;
  under Q190391MemLpTwo they agree with Mathlib's integral and variance.

  Q190391Independent is the finite-family product characterization of
  independence, using the outer measure induced by M so that the definition
  applies to the source's arbitrary functions before measurable
  representatives are selected. Q190391IdentDistrib requires equal
  pushforward laws and retains almost-everywhere measurability.

  Q190391GaussianReal characterizes the zero-mean real Gaussian probability
  measure of any nonnegative variance by its characteristic function,
  including the zero-variance Dirac case. Q190391HasGaussianLaw says that Y
  has exactly this pushforward law.

  Q190391Normalized is the sequence

    n |-> (sqrt n)^(-1) * (sum_(k < n) X_k - n * integral X_0).

  Its inverse-square-root factor is explicitly zero at n = 0, matching Lean's
  totalized inverse, since division by zero has a different junk value in
  SetMM.

  Q190391TendstoInDistribution expands convergence of its pushforward laws by
  the bounded-continuous-test-function characterization of weak convergence.
  The final declaration is the single unproved corpus $a statement. Every
  preceding $a declaration is syntax or a faithful definition, and this
  database contains no $p proof statement.
$)

$c Q190391AERep Q190391AEMeasurable Q190391Measure Q190391Map
   Q190391Square Q190391CenteredSquare Q190391MemLpTwo Q190391Mean
   Q190391Variance Q190391Independent Q190391IdentDistrib
   Q190391Char Q190391GaussianReal Q190391HasGaussianLaw
   Q190391Normalized Q190391BoundedContinuous Q190391WeakTendsto
   Q190391TendstoInDistribution $.

q190391-aerep-syntax
  $a wff ( Q190391AERep M H K ) $.
q190391-aemeasurable-syntax
  $a wff ( Q190391AEMeasurable M H ) $.
q190391-measure-syntax
  $a class ( Q190391Measure M A ) $.
q190391-map-syntax
  $a wff ( Q190391Map M H P ) $.
q190391-square-syntax
  $a class ( Q190391Square M H ) $.
q190391-centered-square-syntax
  $a class ( Q190391CenteredSquare M H m ) $.
q190391-mem-lp-two-syntax
  $a wff ( Q190391MemLpTwo M H ) $.
q190391-mean-syntax
  $a class ( Q190391Mean M H ) $.
q190391-variance-syntax
  $a class ( Q190391Variance M H ) $.
q190391-independent-syntax
  $a wff ( Q190391Independent M X ) $.
q190391-ident-distrib-syntax
  $a wff ( Q190391IdentDistrib M H K ) $.
q190391-char-syntax
  $a class ( Q190391Char t ) $.
q190391-gaussian-real-syntax
  $a wff ( Q190391GaussianReal P v ) $.
q190391-has-gaussian-law-syntax
  $a wff ( Q190391HasGaussianLaw N Y v ) $.
q190391-normalized-syntax
  $a class ( Q190391Normalized M X ) $.
q190391-bounded-continuous-syntax
  $a wff ( Q190391BoundedContinuous H ) $.
q190391-weak-tendsto-syntax
  $a wff ( Q190391WeakTendsto P Q ) $.
q190391-tendsto-in-distribution-syntax
  $a wff ( Q190391TendstoInDistribution M N F Y ) $.

${
  $d H K M Z x $.

  q190391-aerep-definition $a |- (
    ( Q190391AERep M H K )
    <->
    (
      K e. ( dom M MblFnM BrSiga )
      /\
      E. Z e. dom M
        (
          ( M ` Z ) = 0
          /\
          A. x e. ( U. dom M \ Z )
            ( H ` x ) = ( K ` x )
        )
    )
  ) $.
$}

${
  $d H K M $.

  q190391-aemeasurable-definition $a |- (
    ( Q190391AEMeasurable M H )
    <->
    (
      H : U. dom M --> RR
      /\
      E. K ( Q190391AERep M H K )
    )
  ) $.
$}

${
  $d A M $.

  q190391-measure-definition $a |- (
    Q190391Measure M A
  ) = ( ( toOMeas ` M ) ` A ) $.
$}

${
  $d A H K M P $.

  q190391-map-definition $a |- (
    ( Q190391Map M H P )
    <->
    (
      (
        P e. Prob
        /\
        dom P = BrSiga
      )
      /\
      E. K
        (
          ( Q190391AERep M H K )
          /\
          A. A e. BrSiga
            ( P ` A ) = ( M ` ( `' K " A ) )
        )
    )
  ) $.
$}

${
  $d H M x $.

  q190391-square-definition $a |- (
    Q190391Square M H
  ) =
    ( x e. U. dom M |-> ( ( H ` x ) ^ 2 ) )
  $.
$}

${
  $d H M m x $.

  q190391-centered-square-definition $a |- (
    Q190391CenteredSquare M H m
  ) =
    (
      x e. U. dom M |->
      ( ( ( H ` x ) - m ) ^ 2 )
    )
  $.
$}

${
  $d H K M $.

  q190391-mem-lp-two-definition $a |- (
    ( Q190391MemLpTwo M H )
    <->
    (
      H : U. dom M --> RR
      /\
      E. K
        (
          ( Q190391AERep M H K )
          /\
          ( Q190391Square M K ) e. dom ( RRfld itgm M )
        )
    )
  ) $.
$}

${
  $d H K M m $.

  q190391-mean-definition $a |- (
    Q190391Mean M H
  ) =
    U. { m e. RR |
      E. K
        (
          ( Q190391AERep M H K )
          /\
          (
            K e. dom ( RRfld itgm M )
            /\
            ( ( RRfld itgm M ) ` K ) = m
          )
        )
    }
  $.
$}

${
  $d H K M v $.

  q190391-variance-definition $a |- (
    Q190391Variance M H
  ) =
    U. { v e. RR |
      E. K
        (
          ( Q190391AERep M H K )
          /\
          (
            ( Q190391CenteredSquare
              M K ( Q190391Mean M H ) )
              e. dom ( RRfld itgm M )
            /\
            (
              ( RRfld itgm M )
              `
              ( Q190391CenteredSquare
                M K ( Q190391Mean M H ) )
            )
            =
            v
          )
        )
    }
  $.
$}

${
  $d M X f i s $.

  q190391-independent-definition $a |- (
    ( Q190391Independent M X )
    <->
    A. s e. ( Fin i^i ~P NN0 )
      A. f e. ( BrSiga ^m s )
        (
          Q190391Measure
          M
          (
            U. dom M
            i^i
            |^|_ i e. s
              ( `' ( X ` i ) " ( f ` i ) )
          )
        )
        =
        prod_ i e. s
          (
            Q190391Measure
            M
            ( `' ( X ` i ) " ( f ` i ) )
          )
  ) $.
$}

${
  $d H K M P $.

  q190391-ident-distrib-definition $a |- (
    ( Q190391IdentDistrib M H K )
    <->
    (
      ( Q190391AEMeasurable M H )
      /\
      (
        ( Q190391AEMeasurable M K )
        /\
        E. P
          (
            ( Q190391Map M H P )
            /\
            ( Q190391Map M K P )
          )
      )
    )
  ) $.
$}

${
  $d t x $.

  q190391-char-definition $a |- (
    Q190391Char t
  ) =
    (
      x e. RR |->
      (
        exp `
        (
          _i
          x.
          ( t x. x )
        )
      )
    )
  $.
$}

${
  $d P t v $.

  q190391-gaussian-real-definition $a |- (
    ( Q190391GaussianReal P v )
    <->
    (
      (
        P e. Prob
        /\
        dom P = BrSiga
      )
      /\
      (
        v e. ( 0 [,) +oo )
        /\
        A. t e. RR
          (
            ( Q190391Char t )
            e.
            dom ( CCfld itgm P )
            /\
            (
              ( CCfld itgm P )
              `
              ( Q190391Char t )
            )
            =
            (
              exp `
              (
                (
                  ( _i x. 0 )
                  x.
                  t
                )
                -
                (
                  ( v x. ( t ^ 2 ) )
                  /
                  2
                )
              )
            )
          )
      )
    )
  ) $.
$}

${
  $d N P Y v $.

  q190391-has-gaussian-law-definition $a |- (
    ( Q190391HasGaussianLaw N Y v )
    <->
    E. P
      (
        ( Q190391GaussianReal P v )
        /\
        ( Q190391Map N Y P )
      )
  ) $.
$}

${
  $d M X k n x $.

  q190391-normalized-definition $a |- (
    Q190391Normalized M X
  ) =
    (
      n e. NN0 |->
      (
        x e. U. dom M |->
        (
          if (
            n = 0
            ,
            0
            ,
            ( 1 / ( sqrt ` n ) )
          )
          x.
          (
            (
              sum_ k e. ( 0 ..^ n )
                ( ( X ` k ) ` x )
            )
            -
            (
              n
              x.
              ( Q190391Mean M ( X ` 0 ) )
            )
          )
        )
      )
    )
  $.
$}

${
  $d H c x $.

  q190391-bounded-continuous-definition $a |- (
    ( Q190391BoundedContinuous H )
    <->
    (
      H e.
        (
          ( TopOpen ` RRfld )
          Cn
          ( TopOpen ` RRfld )
        )
      /\
      E. c e. RR+
        A. x e. RR
          ( abs ` ( H ` x ) ) < c
    )
  ) $.
$}

${
  $d H P Q n $.

  q190391-weak-tendsto-definition $a |- (
    ( Q190391WeakTendsto P Q )
    <->
    (
      (
        P : NN0 --> Prob
        /\
        A. n e. NN0 dom ( P ` n ) = BrSiga
      )
      /\
      (
        (
          Q e. Prob
          /\
          dom Q = BrSiga
        )
        /\
        A. H
          (
            ( Q190391BoundedContinuous H )
            ->
            (
              n e. NN0 |->
              (
                ( RRfld itgm ( P ` n ) )
                `
                H
              )
            )
            ~~>
            (
              ( RRfld itgm Q )
              `
              H
            )
          )
      )
    )
  ) $.
$}

${
  $d F M N P Q Y n $.

  q190391-tendsto-in-distribution-definition $a |- (
    ( Q190391TendstoInDistribution M N F Y )
    <->
    (
      (
        A. n e. NN0
          ( Q190391AEMeasurable M ( F ` n ) )
        /\
        ( Q190391AEMeasurable N Y )
      )
      /\
      E. P E. Q
        (
          (
            (
              P : NN0 --> Prob
              /\
              Q e. Prob
            )
            /\
            (
              A. n e. NN0
                ( Q190391Map M ( F ` n ) ( P ` n ) )
              /\
              ( Q190391Map N Y Q )
            )
          )
          /\
          ( Q190391WeakTendsto P Q )
        )
    )
  ) $.
$}

${
  $d A F H K M N P Q X Y Z c f i k m n s t v x $.

  thousand-theorems-q190391-central-limit-theorem $a |-
    A. M e. Prob A. N e. Prob
      A. X e. ( ( RR ^m U. dom M ) ^m NN0 )
        A. Y e. ( RR ^m U. dom N )
          (
            (
              (
                Q190391HasGaussianLaw
                N
                Y
                ( Q190391Variance M ( X ` 0 ) )
              )
              /\
              (
                ( Q190391MemLpTwo M ( X ` 0 ) )
                /\
                (
                  ( Q190391Independent M X )
                  /\
                  A. i e. NN0
                    (
                      Q190391IdentDistrib
                      M
                      ( X ` i )
                      ( X ` 0 )
                    )
                )
              )
            )
            ->
            (
              Q190391TendstoInDistribution
              M
              N
              ( Q190391Normalized M X )
              Y
            )
          )
  $.
$}
