$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1067156
  (thousand-theorems__metamath__Q1067156), "Dominated convergence theorem":
  a sequence of almost-everywhere strongly measurable functions into an
  arbitrary real normed vector space, dominated in norm almost everywhere by
  an integrable real function and converging almost everywhere pointwise, has
  convergent totalized Bochner integrals. The Bochner integral is encoded by
  L1-approximation with integrable measurable finite-range functions. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1067156Tendsto W S z is convergence of the NN0-indexed sequence S to z in
  the norm topology of W.

  Q1067156AEStrong M W H expresses almost-everywhere strong measurability:
  outside one M-null measurable set, H is the pointwise limit of a sequence
  of finite-range Borel-measurable functions. This is the standard simple-
  function characterization of Lean's AEStronglyMeasurable predicate.

  Q1067156Simple, Q1067156SimpleIntegral, and Q1067156LIntegral define the
  lower Lebesgue integral of a nonnegative extended-real-valued function.
  Q1067156Integrable M W H is almost-everywhere strong measurability together
  with finiteness of the lower integral of the pointwise norm, matching Lean's
  Integrable predicate on arbitrary measure spaces and arbitrary real normed
  codomains.

  Q1067156HasIntegral M W H y says that H is approximated in L1 by a sequence
  of measurable finite-range functions in the domain of SetMM's simple
  Bochner integral, whose integrals converge to y. Q1067156Integral W M H is
  the unique such y when W is complete and H is integrable, and is the zero
  vector otherwise. Thus it is Lean's totalized Bochner integral without
  imposing completeness or integrability as additional theorem assumptions.

  Q1067156AELe M W H b is the almost-everywhere bound norm(H(x)) <= b(x), and
  Q1067156AELimit M W F f is almost-everywhere pointwise convergence F_n(x)
  to f(x). The final declaration is the single unproved corpus $a statement;
  the preceding $a declarations are syntax and faithful definitions only.
$)

$c Q1067156Tendsto Q1067156AEStrong
   Q1067156Simple Q1067156SimpleIntegral Q1067156LIntegral
   Q1067156Diff Q1067156L1Distance Q1067156Integrable
   Q1067156HasIntegral Q1067156Integral
   Q1067156AELe Q1067156AELimit $.

q1067156-tendsto-syntax $a wff ( Q1067156Tendsto W S z ) $.
q1067156-aestrong-syntax $a wff ( Q1067156AEStrong M W H ) $.
q1067156-simple-syntax $a wff ( Q1067156Simple M G ) $.
q1067156-simple-integral-syntax
  $a class ( Q1067156SimpleIntegral M G ) $.
q1067156-lintegral-syntax $a class ( Q1067156LIntegral M H ) $.
q1067156-diff-syntax $a class ( Q1067156Diff M W H K ) $.
q1067156-l1-distance-syntax
  $a class ( Q1067156L1Distance M W H K ) $.
q1067156-integrable-syntax $a wff ( Q1067156Integrable M W H ) $.
q1067156-has-integral-syntax
  $a wff ( Q1067156HasIntegral M W H y ) $.
q1067156-integral-syntax $a class ( Q1067156Integral W M H ) $.
q1067156-aele-syntax $a wff ( Q1067156AELe M W H b ) $.
q1067156-aelimit-syntax $a wff ( Q1067156AELimit M W F f ) $.

${
  $d S W z $.

  q1067156-tendsto-definition $a |- (
    ( Q1067156Tendsto W S z )
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

  q1067156-aestrong-definition $a |- (
    ( Q1067156AEStrong M W H )
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
                  Q1067156Tendsto
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

  q1067156-simple-definition $a |- (
    ( Q1067156Simple M G )
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

  q1067156-simple-integral-definition $a |- (
    Q1067156SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q1067156-lintegral-definition $a |- (
    Q1067156LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q1067156Simple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q1067156SimpleIntegral M G )
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

  q1067156-diff-definition $a |- (
    Q1067156Diff M W H K
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

  q1067156-l1-distance-definition $a |- (
    Q1067156L1Distance M W H K
  ) =
    (
      Q1067156LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q1067156Diff M W H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M W x $.

  q1067156-integrable-definition $a |- (
    ( Q1067156Integrable M W H )
    <->
    (
      ( Q1067156AEStrong M W H )
      /\
      (
        Q1067156LIntegral
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

  q1067156-has-integral-definition $a |- (
    ( Q1067156HasIntegral M W H y )
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
            Q1067156Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q1067156L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q1067156Tendsto
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

  q1067156-integral-definition $a |- (
    Q1067156Integral W M H
    =
    if
    (
      (
        W e. CMetSp
        /\
        ( Q1067156Integrable M W H )
      ) ,
      (
        iota_ y e. ( Base ` W )
          ( Q1067156HasIntegral M W H y )
      ) ,
      ( 0g ` W )
    )
  ) $.
$}

${
  $d H M N W b x $.

  q1067156-aele-definition $a |- (
    ( Q1067156AELe M W H b )
    <->
    E. N e. dom M
      (
        ( M ` N ) = 0
        /\
        A. x e. ( U. dom M \ N )
          ( ( ( norm ` W ) ` ( H ` x ) ) <_ ( b ` x ) )
      )
  ) $.
$}

${
  $d F M N W f n x $.

  q1067156-aelimit-definition $a |- (
    ( Q1067156AELimit M W F f )
    <->
    E. N e. dom M
      (
        ( M ` N ) = 0
        /\
        A. x e. ( U. dom M \ N )
          (
            Q1067156Tendsto
            W
            ( n e. NN0 |-> ( ( F ` n ) ` x ) )
            ( f ` x )
          )
      )
  ) $.
$}

${
  $d F M W b f n w $.

  thousand-theorems-q1067156-dominated-convergence $a |-
    A. M e. U. ran measures
      A. W e. { w e. NrmVec | ( Scalar ` w ) = RRfld }
        A. F e. ( ( ( Base ` W ) ^m U. dom M ) ^m NN0 )
          A. f e. ( ( Base ` W ) ^m U. dom M )
            A. b e. ( RR ^m U. dom M )
              (
                (
                  (
                    A. n e. NN0
                      ( Q1067156AEStrong M W ( F ` n ) )
                    /\
                    ( Q1067156Integrable M RRfld b )
                  )
                  /\
                  (
                    A. n e. NN0
                      ( Q1067156AELe M W ( F ` n ) b )
                    /\
                    ( Q1067156AELimit M W F f )
                  )
                )
                ->
                (
                  Q1067156Tendsto
                  W
                  ( n e. NN0 |->
                    ( Q1067156Integral W M ( F ` n ) ) )
                  ( Q1067156Integral W M f )
                )
              )
  $.
$}
