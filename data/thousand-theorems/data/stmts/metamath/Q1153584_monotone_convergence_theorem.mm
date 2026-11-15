$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1153584
  (thousand-theorems__metamath__Q1153584), "Monotone convergence theorem":
  almost-everywhere monotone convergence for extended-nonnegative Lebesgue
  integrals and antitone convergence for integrable real-valued Bochner
  integrals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1153584Simple and Q1153584SimpleIntegral describe finite-range measurable
  extended-nonnegative simple functions and their integrals.
  Q1153584LIntegral is the lower Lebesgue integral, defined as the supremum of
  the integrals of simple functions bounded by its argument.

  Q1153584AEMeasurable says that a function agrees outside a measurable null
  set with a measurable function. Q1153584AEMonotone and
  Q1153584AEAntitone state the respective pointwise order properties outside
  a measurable null set. Q1153584AELimit is almost-everywhere pointwise
  sequence convergence in the indicated topology. These are equivalent to
  the Lean almost-everywhere predicates because every measure-zero exceptional
  set is contained in a measurable measure-zero set.

  Q1153584AEStrong is the simple-function characterization of almost-
  everywhere strong measurability. Q1153584Integrable is almost-everywhere
  strong measurability together with finiteness of the lower integral of the
  pointwise norm. Q1153584HasIntegral says that a function is approximated in
  L1 by measurable finite-range functions whose simple Bochner integrals
  converge, and Q1153584Integral is that unique limit for an integrable real
  function and zero otherwise. This avoids SetMM's unfinished general itgm
  operator while matching Lean's totalized real Bochner integral.

  Q1153584Tendsto uses SetMM's native NN0-indexed sequence convergence. The
  two final unproved $a declarations render respectively the extended-
  nonnegative monotone theorem and the real-valued antitone theorem. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q1153584Simple Q1153584SimpleIntegral Q1153584LIntegral
   Q1153584Tendsto Q1153584AEMeasurable Q1153584AEMonotone
   Q1153584AEAntitone Q1153584AELimit Q1153584AEStrong
   Q1153584Diff Q1153584L1Distance Q1153584Integrable
   Q1153584HasIntegral Q1153584Integral $.

q1153584-simple-syntax $a wff ( Q1153584Simple M G ) $.
q1153584-simple-integral-syntax
  $a class ( Q1153584SimpleIntegral M G ) $.
q1153584-lintegral-syntax $a class ( Q1153584LIntegral M H ) $.
q1153584-tendsto-syntax $a wff ( Q1153584Tendsto W S z ) $.
q1153584-aemeasurable-syntax
  $a wff ( Q1153584AEMeasurable M H ) $.
q1153584-aemonotone-syntax
  $a wff ( Q1153584AEMonotone M F ) $.
q1153584-aeantitone-syntax
  $a wff ( Q1153584AEAntitone M F ) $.
q1153584-aelimit-syntax
  $a wff ( Q1153584AELimit M W F H ) $.
q1153584-aestrong-syntax
  $a wff ( Q1153584AEStrong M W H ) $.
q1153584-diff-syntax
  $a class ( Q1153584Diff M W H K ) $.
q1153584-l1-distance-syntax
  $a class ( Q1153584L1Distance M W H K ) $.
q1153584-integrable-syntax
  $a wff ( Q1153584Integrable M H ) $.
q1153584-has-integral-syntax
  $a wff ( Q1153584HasIntegral M H y ) $.
q1153584-integral-syntax
  $a class ( Q1153584Integral M H ) $.

${
  $d G M $.

  q1153584-simple-definition $a |- (
    ( Q1153584Simple M G )
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

  q1153584-simple-integral-definition $a |- (
    Q1153584SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q1153584-lintegral-definition $a |- (
    Q1153584LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q1153584Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q1153584SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d S W z $.

  q1153584-tendsto-definition $a |- (
    ( Q1153584Tendsto W S z )
    <->
    (
      S : NN0 --> ( Base ` W )
      /\
      S ( ~~>t ` ( TopOpen ` W ) ) z
    )
  ) $.
$}

${
  $d G H M N x $.

  q1153584-aemeasurable-definition $a |- (
    ( Q1153584AEMeasurable M H )
    <->
    (
      H : U. dom M --> ( 0 [,] +oo )
      /\
      E. G
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
          E. N e. dom M
            (
              ( M ` N ) = 0
              /\
              A. x e. ( U. dom M \ N )
                ( H ` x ) = ( G ` x )
            )
        )
    )
  ) $.
$}

${
  $d F M N m n x $.

  q1153584-aemonotone-definition $a |- (
    ( Q1153584AEMonotone M F )
    <->
    E. N e. dom M
      (
        ( M ` N ) = 0
        /\
        A. x e. ( U. dom M \ N )
          A. n e. NN0
            A. m e. NN0
              (
                n <_ m
                ->
                ( ( F ` n ) ` x ) <_ ( ( F ` m ) ` x )
              )
      )
  ) $.
$}

${
  $d F M N m n x $.

  q1153584-aeantitone-definition $a |- (
    ( Q1153584AEAntitone M F )
    <->
    E. N e. dom M
      (
        ( M ` N ) = 0
        /\
        A. x e. ( U. dom M \ N )
          A. n e. NN0
            A. m e. NN0
              (
                n <_ m
                ->
                ( ( F ` m ) ` x ) <_ ( ( F ` n ) ` x )
              )
      )
  ) $.
$}

${
  $d F H M N W n x $.

  q1153584-aelimit-definition $a |- (
    ( Q1153584AELimit M W F H )
    <->
    E. N e. dom M
      (
        ( M ` N ) = 0
        /\
        A. x e. ( U. dom M \ N )
          (
            Q1153584Tendsto
            W
            ( n e. NN0 |-> ( ( F ` n ) ` x ) )
            ( H ` x )
          )
      )
  ) $.
$}

${
  $d H M N S W n x $.

  q1153584-aestrong-definition $a |- (
    ( Q1153584AEStrong M W H )
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
                  Q1153584Tendsto
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
  $d H K M W x $.

  q1153584-diff-definition $a |- (
    Q1153584Diff M W H K
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

  q1153584-l1-distance-definition $a |- (
    Q1153584L1Distance M W H K
  ) =
    (
      Q1153584LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q1153584Diff M W H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M x $.

  q1153584-integrable-definition $a |- (
    ( Q1153584Integrable M H )
    <->
    (
      ( Q1153584AEStrong M RRfld H )
      /\
      (
        Q1153584LIntegral
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
  $d H M S n y $.

  q1153584-has-integral-definition $a |- (
    ( Q1153584HasIntegral M H y )
    <->
    (
      y e. RR
      /\
      E. S e. ( ( RR ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            ( ( S ` n ) e. dom ( RRfld sitg M ) )
          /\
          (
            Q1153584Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q1153584L1Distance M RRfld H ( S ` n ) ) )
            0
            /\
            Q1153584Tendsto
            RRfld
            ( n e. NN0 |-> ( ( RRfld sitg M ) ` ( S ` n ) ) )
            y
          )
        )
    )
  ) $.
$}

${
  $d H M y $.

  q1153584-integral-definition $a |- (
    Q1153584Integral M H
    =
    if
    (
      ( Q1153584Integrable M H ) ,
      (
        iota_ y e. RR
          ( Q1153584HasIntegral M H y )
      ) ,
      0
    )
  ) $.
$}

${
  $d F G H M N S W f m n x y z $.

  thousand-theorems-q1153584-lintegral-monotone-convergence $a |-
    A. M e. U. ran measures
      A. F e.
        ( ( ( 0 [,] +oo ) ^m U. dom M ) ^m NN0 )
        A. f e. ( ( 0 [,] +oo ) ^m U. dom M )
          (
            (
              (
                A. n e. NN0
                  ( Q1153584AEMeasurable M ( F ` n ) )
                /\
                ( Q1153584AEMonotone M F )
              )
              /\
              (
                Q1153584AELimit
                M
                ( RR*s |`s ( 0 [,] +oo ) )
                F
                f
              )
            )
            ->
            (
              Q1153584Tendsto
              ( RR*s |`s ( 0 [,] +oo ) )
              ( n e. NN0 |->
                ( Q1153584LIntegral M ( F ` n ) ) )
              ( Q1153584LIntegral M f )
            )
          )
  $.
$}

${
  $d F G H M N S W f m n x y z $.

  thousand-theorems-q1153584-integral-antitone-convergence $a |-
    A. M e. U. ran measures
      A. F e. ( ( RR ^m U. dom M ) ^m NN0 )
        A. f e. ( RR ^m U. dom M )
          (
            (
              (
                A. n e. NN0
                  ( Q1153584Integrable M ( F ` n ) )
                /\
                ( Q1153584Integrable M f )
              )
              /\
              (
                ( Q1153584AEAntitone M F )
                /\
                ( Q1153584AELimit M RRfld F f )
              )
            )
            ->
            (
              Q1153584Tendsto
              RRfld
              ( n e. NN0 |->
                ( Q1153584Integral M ( F ` n ) ) )
              ( Q1153584Integral M f )
            )
          )
  $.
$}
