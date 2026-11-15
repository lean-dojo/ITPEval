$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2027347
  (thousand-theorems__metamath__Q2027347), "Optional stopping theorem":
  under a sigma-finite filtration, a strongly adapted integrable real-valued
  process is a submartingale exactly when expected stopped values are monotone
  for every ordered pair of bounded stopping times. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q2027347Filtration says that F is an increasing NN0-indexed family of
  sub-sigma-algebras of the measurable space of M.

  Q2027347SigmaFiniteFiltration says that at every filtration level the sample
  space has a countable cover by level-measurable sets of finite M-measure.
  This is the sigma-finiteness of M viewed on that sub-sigma-algebra.

  Q2027347StronglyAdapted requires each real-valued X_n to be measurable for
  the nth filtration sigma-algebra. For real-valued functions this is
  equivalent to strong measurability. Q2027347FunctionIntegrable is almost-
  everywhere strong measurability together with finite L1 norm, and
  Q2027347Integrable applies it to every process slice.

  Q2027347Integral is the totalized real Bochner integral defined by limits of
  simple integrals along L1-approximating measurable finite-range functions.
  Q2027347SetIntegral is the integral of the zero extension from an event.
  Q2027347Submartingale uses the equivalent set-integral characterization:
  adaptedness, integrability, and monotonicity of these integrals on every
  earlier-filtration event. Under Q2027347SigmaFiniteFiltration this is
  equivalent to the conditional-expectation definition in the Lean source.

  A stopping time maps the sample space to NN0* = NN0 u. { +oo }, with
  { x | T(x) <= n } measurable at level n. Q2027347StoppingLe is pointwise
  order, and Q2027347Bounded keeps the natural bound existentially quantified
  inside the stopping-time condition. Q2027347Stopped evaluates X at a finite
  stopping value and uses index 0 at +oo, representing the arbitrary natural
  index selected by stoppedValue there. In the final assertion the boundedness
  and order hypotheses force both stopping times to be finite.

  The final $a declaration is the translated equivalence. All preceding $a
  declarations are syntax or faithful definitions; there is no $p statement.
$)

$c Q2027347Filtration Q2027347SigmaFiniteFiltration
   Q2027347StronglyAdapted Q2027347SeqTendsto
   Q2027347Simple Q2027347SimpleIntegral Q2027347LIntegral
   Q2027347AEStrong Q2027347Diff Q2027347L1Distance
   Q2027347FunctionIntegrable Q2027347HasIntegral Q2027347Integral
   Q2027347Integrable Q2027347SetIntegral
   Q2027347Submartingale Q2027347Stopping Q2027347StoppingLe
   Q2027347Bounded Q2027347Stopped $.

q2027347-filtration-syntax
  $a wff ( Q2027347Filtration M F ) $.
q2027347-sigma-finite-filtration-syntax
  $a wff ( Q2027347SigmaFiniteFiltration M F ) $.
q2027347-strongly-adapted-syntax
  $a wff ( Q2027347StronglyAdapted M F X ) $.
q2027347-seq-tendsto-syntax
  $a wff ( Q2027347SeqTendsto W S z ) $.
q2027347-simple-syntax
  $a wff ( Q2027347Simple M G ) $.
q2027347-simple-integral-syntax
  $a class ( Q2027347SimpleIntegral M G ) $.
q2027347-lintegral-syntax
  $a class ( Q2027347LIntegral M H ) $.
q2027347-aestrong-syntax
  $a wff ( Q2027347AEStrong M H ) $.
q2027347-diff-syntax
  $a class ( Q2027347Diff M H K ) $.
q2027347-l1-distance-syntax
  $a class ( Q2027347L1Distance M H K ) $.
q2027347-function-integrable-syntax
  $a wff ( Q2027347FunctionIntegrable M H ) $.
q2027347-has-integral-syntax
  $a wff ( Q2027347HasIntegral M H y ) $.
q2027347-integral-syntax
  $a class ( Q2027347Integral M H ) $.
q2027347-integrable-syntax
  $a wff ( Q2027347Integrable M X ) $.
q2027347-set-integral-syntax
  $a class ( Q2027347SetIntegral M H A ) $.
q2027347-submartingale-syntax
  $a wff ( Q2027347Submartingale M F X ) $.
q2027347-stopping-syntax
  $a wff ( Q2027347Stopping M F T ) $.
q2027347-stopping-le-syntax
  $a wff ( Q2027347StoppingLe M T S ) $.
q2027347-bounded-syntax
  $a wff ( Q2027347Bounded M T ) $.
q2027347-stopped-syntax
  $a class ( Q2027347Stopped M X T ) $.

${
  $d F M i j $.

  q2027347-filtration-definition $a |- (
    ( Q2027347Filtration M F )
    <->
    (
      F : NN0 --> ( sigAlgebra ` U. dom M )
      /\
      (
        A. i e. NN0 ( F ` i ) C_ dom M
        /\
        A. i e. NN0 A. j e. NN0
          (
            i <_ j
            ->
            ( F ` i ) C_ ( F ` j )
          )
      )
    )
  ) $.
$}

${
  $d C F M k n $.

  q2027347-sigma-finite-filtration-definition $a |- (
    ( Q2027347SigmaFiniteFiltration M F )
    <->
    A. n e. NN0
      E. C e. ( ( F ` n ) ^m NN0 )
        (
          A. k e. NN0 ( M ` ( C ` k ) ) < +oo
          /\
          U. ran C = U. dom M
        )
  ) $.
$}

${
  $d F M X n $.

  q2027347-strongly-adapted-definition $a |- (
    ( Q2027347StronglyAdapted M F X )
    <->
    (
      X : NN0 --> ( RR ^m U. dom M )
      /\
      A. n e. NN0
        ( X ` n ) e. ( ( F ` n ) MblFnM BrSiga )
    )
  ) $.
$}

${
  $d S W z $.

  q2027347-seq-tendsto-definition $a |- (
    ( Q2027347SeqTendsto W S z )
    <->
    (
      S : NN0 --> ( Base ` W )
      /\
      S ( ~~>t ` ( TopOpen ` W ) ) z
    )
  ) $.
$}

${
  $d G M $.

  q2027347-simple-definition $a |- (
    ( Q2027347Simple M G )
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

  q2027347-simple-integral-definition $a |- (
    Q2027347SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q2027347-lintegral-definition $a |- (
    Q2027347LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q2027347Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q2027347SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d H M N s n x $.

  q2027347-aestrong-definition $a |- (
    ( Q2027347AEStrong M H )
    <->
    (
      H e. ( RR ^m U. dom M )
      /\
      E. s e. ( ( RR ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            (
              ( s ` n ) e. ( dom M MblFnM BrSiga )
              /\
              ran ( s ` n ) e. Fin
            )
          /\
          E. N e. dom M
            (
              ( M ` N ) = 0
              /\
              A. x e. ( U. dom M \ N )
                (
                  Q2027347SeqTendsto
                  RRfld
                  ( n e. NN0 |-> ( ( s ` n ) ` x ) )
                  ( H ` x )
                )
            )
        )
    )
  ) $.
$}

${
  $d H K M x $.

  q2027347-diff-definition $a |- (
    Q2027347Diff M H K
  ) =
    ( x e. U. dom M |->
      (
        ( H ` x )
        ( +g ` RRfld )
        ( ( -g ` RRfld ) ` ( K ` x ) )
      )
    )
  $.
$}

${
  $d H K M x $.

  q2027347-l1-distance-definition $a |- (
    Q2027347L1Distance M H K
  ) =
    (
      Q2027347LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` RRfld )
          `
          ( ( Q2027347Diff M H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M x $.

  q2027347-function-integrable-definition $a |- (
    ( Q2027347FunctionIntegrable M H )
    <->
    (
      ( Q2027347AEStrong M H )
      /\
      (
        Q2027347LIntegral
        M
        ( x e. U. dom M |->
          ( ( norm ` RRfld ) ` ( H ` x ) )
        )
      )
      < +oo
    )
  ) $.
$}

${
  $d H M n s y $.

  q2027347-has-integral-definition $a |- (
    ( Q2027347HasIntegral M H y )
    <->
    (
      y e. RR
      /\
      E. s e. ( ( RR ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            ( ( s ` n ) e. dom ( RRfld sitg M ) )
          /\
          (
            Q2027347SeqTendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q2027347L1Distance M H ( s ` n ) ) )
            0
            /\
            Q2027347SeqTendsto
            RRfld
            ( n e. NN0 |-> ( ( RRfld sitg M ) ` ( s ` n ) ) )
            y
          )
        )
    )
  ) $.
$}

${
  $d H M y $.

  q2027347-integral-definition $a |- (
    Q2027347Integral M H
    =
    if
    (
      ( Q2027347FunctionIntegrable M H ) ,
      (
        iota_ y e. RR
          ( Q2027347HasIntegral M H y )
      ) ,
      0
    )
  ) $.
$}

${
  $d M X n $.

  q2027347-integrable-definition $a |- (
    ( Q2027347Integrable M X )
    <->
    (
      X : NN0 --> ( RR ^m U. dom M )
      /\
      A. n e. NN0
        ( Q2027347FunctionIntegrable M ( X ` n ) )
    )
  ) $.
$}

${
  $d A H M x $.

  q2027347-set-integral-definition $a |- (
    Q2027347SetIntegral M H A
  ) =
    (
      Q2027347Integral
      M
      ( x e. U. dom M |->
        if
        (
          x e. A ,
          ( H ` x ) ,
          0
        )
      )
    )
  $.
$}

${
  $d A F M X i j $.

  q2027347-submartingale-definition $a |- (
    ( Q2027347Submartingale M F X )
    <->
    (
      ( Q2027347StronglyAdapted M F X )
      /\
      (
        ( Q2027347Integrable M X )
        /\
        A. i e. NN0 A. j e. NN0
          (
            i <_ j
            ->
            A. A e. ( F ` i )
              (
                ( Q2027347SetIntegral M ( X ` i ) A )
                <_
                ( Q2027347SetIntegral M ( X ` j ) A )
              )
          )
      )
    )
  ) $.
$}

${
  $d F M T n x $.

  q2027347-stopping-definition $a |- (
    ( Q2027347Stopping M F T )
    <->
    (
      T : U. dom M --> NN0*
      /\
      A. n e. NN0
        { x e. U. dom M | ( T ` x ) <_ n } e. ( F ` n )
    )
  ) $.
$}

${
  $d M S T x $.

  q2027347-stopping-le-definition $a |- (
    ( Q2027347StoppingLe M T S )
    <->
    A. x e. U. dom M
      ( T ` x ) <_ ( S ` x )
  ) $.
$}

${
  $d M T N x $.

  q2027347-bounded-definition $a |- (
    ( Q2027347Bounded M T )
    <->
    E. N e. NN0
      A. x e. U. dom M
        ( T ` x ) <_ N
  ) $.
$}

${
  $d M T X x $.

  q2027347-stopped-definition $a |- (
    Q2027347Stopped M X T
  ) =
    ( x e. U. dom M |->
      if
      (
        ( T ` x ) e. NN0 ,
        ( ( X ` ( T ` x ) ) ` x ) ,
        ( ( X ` 0 ) ` x )
      )
    )
  $.
$}

${
  $d A C F H M N S T X i j k n x $.

  thousand-theorems-q2027347-optional-stopping $a |-
    A. M e. U. ran measures
      A. F A. X
        (
          (
            (
              ( Q2027347Filtration M F )
              /\
              ( Q2027347SigmaFiniteFiltration M F )
            )
            /\
            (
              ( Q2027347StronglyAdapted M F X )
              /\
              ( Q2027347Integrable M X )
            )
          )
          ->
          (
            ( Q2027347Submartingale M F X )
            <->
            A. T A. S
              (
                ( Q2027347Stopping M F T )
                ->
                (
                  ( Q2027347Stopping M F S )
                  ->
                  (
                    ( Q2027347StoppingLe M T S )
                    ->
                    (
                      ( Q2027347Bounded M S )
                      ->
                      (
                        ( Q2027347Integral
                          M ( Q2027347Stopped M X T ) )
                        <_
                        ( Q2027347Integral
                          M ( Q2027347Stopped M X S ) )
                      )
                    )
                  )
                )
              )
          )
        )
  $.
$}
