$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1217677
  (thousand-theorems__metamath__Q1217677), "Fundamental theorem of calculus":
  an integrand that is locally almost-everywhere strongly measurable and has
  an almost-everywhere finite limit at an endpoint gives a strict derivative
  of its directed Bochner interval integral, and a continuous function with
  an interval-integrable right derivative satisfies the integral difference
  formula in an arbitrary complete real normed vector space. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1217677Restrict is the zero extension of F from the open real interval
  (A,B). Using the open interval instead of Lean's half-open interval changes
  only Lebesgue-null endpoints. Q1217677IntervalIntegrable requires the two
  endpoint orders, exactly as Lean's directed IntervalIntegrable predicate.
  Q1217677AEStrong and Q1217677FunctionIntegrable encode Lean's
  AEStronglyMeasurable and Integrable predicates. Q1217677HasIntegral defines
  the Bochner integral by L1-approximation with measurable finite-range
  functions, and Q1217677TotalIntegral totalizes its unique value by zero.
  Q1217677Integral is the corresponding directed interval integral.

  Q1217677StronglyMeasurableAt gives the finite-range measurable-function
  characterization of strong measurability almost everywhere on a
  neighborhood of B, permitting one measurable Lebesgue-null exceptional set.
  Q1217677AETendstoAt is convergence to C along the infimum of the neighborhood
  filter at B and the Lebesgue almost-everywhere filter.

  Q1217677HasStrictDerivAt is the two-point strict derivative estimate.
  Q1217677ContinuousOn is relative continuity on a set, and
  Q1217677HasRightDerivAt is the derivative within the open right ray. The two
  final $a declarations are the requested unproved corpus statements; every
  preceding $a declaration is syntax or an explicit definition.
$)

$c Q1217677Restrict Q1217677Tendsto Q1217677AEStrong
   Q1217677Simple Q1217677SimpleIntegral Q1217677LIntegral
   Q1217677Diff Q1217677L1Distance Q1217677FunctionIntegrable
   Q1217677HasIntegral Q1217677TotalIntegral
   Q1217677IntervalIntegrable Q1217677Integral
   Q1217677StronglyMeasurableAt
   Q1217677AETendstoAt Q1217677HasStrictDerivAt Q1217677ContinuousOn
   Q1217677HasRightDerivAt $.

q1217677-restrict-syntax $a class
  ( Q1217677Restrict W F A B ) $.
q1217677-tendsto-syntax $a wff
  ( Q1217677Tendsto W S C ) $.
q1217677-aestrong-syntax $a wff
  ( Q1217677AEStrong M W H ) $.
q1217677-simple-syntax $a wff
  ( Q1217677Simple M G ) $.
q1217677-simple-integral-syntax $a class
  ( Q1217677SimpleIntegral M G ) $.
q1217677-lintegral-syntax $a class
  ( Q1217677LIntegral M H ) $.
q1217677-diff-syntax $a class
  ( Q1217677Diff M W H K ) $.
q1217677-l1-distance-syntax $a class
  ( Q1217677L1Distance M W H K ) $.
q1217677-function-integrable-syntax $a wff
  ( Q1217677FunctionIntegrable M W H ) $.
q1217677-has-integral-syntax $a wff
  ( Q1217677HasIntegral M W H y ) $.
q1217677-total-integral-syntax $a class
  ( Q1217677TotalIntegral W H ) $.
q1217677-interval-integrable-syntax $a wff
  ( Q1217677IntervalIntegrable W F A B ) $.
q1217677-integral-syntax $a class
  ( Q1217677Integral W F A B ) $.
q1217677-strongly-measurable-at-syntax $a wff
  ( Q1217677StronglyMeasurableAt W F B ) $.
q1217677-ae-tendsto-at-syntax $a wff
  ( Q1217677AETendstoAt W F B C ) $.
q1217677-has-strict-deriv-at-syntax $a wff
  ( Q1217677HasStrictDerivAt W G C B ) $.
q1217677-continuous-on-syntax $a wff
  ( Q1217677ContinuousOn W F U ) $.
q1217677-has-right-deriv-at-syntax $a wff
  ( Q1217677HasRightDerivAt W F C X ) $.

${
  $d x A $.
  $d x B $.
  $d x F $.
  $d x W $.

  q1217677-restrict-definition $a |- (
    Q1217677Restrict W F A B
  ) =
    ( x e. RR |->
      if
      (
        x e. ( A (,) B ) ,
        ( F ` x ) ,
        ( 0g ` W )
      )
    )
  $.
$}

${
  $d C S W $.

  q1217677-tendsto-definition $a |- (
    ( Q1217677Tendsto W S C )
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

  q1217677-aestrong-definition $a |- (
    ( Q1217677AEStrong M W H )
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
                  Q1217677Tendsto
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

  q1217677-simple-definition $a |- (
    ( Q1217677Simple M G )
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

  q1217677-simple-integral-definition $a |- (
    Q1217677SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q1217677-lintegral-definition $a |- (
    Q1217677LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q1217677Simple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q1217677SimpleIntegral M G )
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

  q1217677-diff-definition $a |- (
    Q1217677Diff M W H K
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

  q1217677-l1-distance-definition $a |- (
    Q1217677L1Distance M W H K
  ) =
    (
      Q1217677LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q1217677Diff M W H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M W x $.

  q1217677-function-integrable-definition $a |- (
    ( Q1217677FunctionIntegrable M W H )
    <->
    (
      ( Q1217677AEStrong M W H )
      /\
      (
        Q1217677LIntegral
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

  q1217677-has-integral-definition $a |- (
    ( Q1217677HasIntegral M W H y )
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
            Q1217677Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q1217677L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q1217677Tendsto
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

  q1217677-total-integral-definition $a |- (
    Q1217677TotalIntegral W H
  ) =
    if
    (
      (
        W e. CMetSp
        /\
        ( Q1217677FunctionIntegrable vol W H )
      ) ,
      (
        iota_ y e. ( Base ` W )
          ( Q1217677HasIntegral vol W H y )
      ) ,
      ( 0g ` W )
    )
  $.
$}

${
  $d A B F W $.

  q1217677-interval-integrable-definition $a |- (
    ( Q1217677IntervalIntegrable W F A B )
    <->
    (
      (
        Q1217677FunctionIntegrable
        vol
        W
        ( Q1217677Restrict W F A B )
      )
      /\
      (
        Q1217677FunctionIntegrable
        vol
        W
        ( Q1217677Restrict W F B A )
      )
    )
  ) $.
$}

${
  $d A B F W $.

  q1217677-integral-definition $a |- (
    Q1217677Integral W F A B
  ) =
    if
    (
      A <_ B ,
      (
        Q1217677TotalIntegral
        W
        ( Q1217677Restrict W F A B )
      ) ,
      (
        ( -g ` W )
        `
        (
          Q1217677TotalIntegral
          W
          ( Q1217677Restrict W F B A )
        )
      )
    )
  $.
$}

${
  $d B F N S W d n x $.

  q1217677-strongly-measurable-at-definition $a |- (
    ( Q1217677StronglyMeasurableAt W F B )
    <->
    E. d e. RR+
      E. S e. ( ( ( Base ` W ) ^m RR ) ^m NN0 )
        (
          A. n e. NN0
            (
              ( S ` n )
                e. ( dom vol MblFnM ( sigaGen ` ( TopOpen ` W ) ) )
              /\
              ran ( S ` n ) e. Fin
            )
          /\
          E. N e. dom vol
            (
              ( vol ` N ) = 0
              /\
              A. x e. ( ( ( B - d ) (,) ( B + d ) ) \ N )
                (
                  Q1217677Tendsto
                  W
                  ( n e. NN0 |-> ( ( S ` n ) ` x ) )
                  ( F ` x )
                )
            )
        )
  ) $.
$}

${
  $d B C F N W d e x $.

  q1217677-ae-tendsto-at-definition $a |- (
    ( Q1217677AETendstoAt W F B C )
    <->
    A. e e. RR+
      E. d e. RR+
        E. N e. dom vol
          (
            ( vol ` N ) = 0
            /\
            A. x e. ( ( ( B - d ) (,) ( B + d ) ) \ N )
              (
                (
                  ( norm ` W )
                  `
                  (
                    ( F ` x )
                    ( +g ` W )
                    ( ( -g ` W ) ` C )
                  )
                )
                <
                e
              )
          )
  ) $.
$}

${
  $d B C G W d e x y $.

  q1217677-has-strict-deriv-at-definition $a |- (
    ( Q1217677HasStrictDerivAt W G C B )
    <->
    (
      G : RR --> ( Base ` W )
      /\
      A. e e. RR+
        E. d e. RR+
          A. x e. ( ( B - d ) (,) ( B + d ) )
            A. y e. ( ( B - d ) (,) ( B + d ) )
              (
                (
                  ( norm ` W )
                  `
                  (
                    (
                      ( G ` y )
                      ( +g ` W )
                      ( ( -g ` W ) ` ( G ` x ) )
                    )
                    ( +g ` W )
                    (
                      ( -g ` W )
                      `
                      ( ( y - x ) ( .s ` W ) C )
                    )
                  )
                )
                <_
                ( e x. ( abs ` ( y - x ) ) )
              )
    )
  ) $.
$}

${
  $d F U W d e x y $.

  q1217677-continuous-on-definition $a |- (
    ( Q1217677ContinuousOn W F U )
    <->
    A. x e. U
      A. e e. RR+
        E. d e. RR+
          A. y e. U
            (
              ( ( abs ` ( y - x ) ) < d )
              ->
              (
                (
                  ( norm ` W )
                  `
                  (
                    ( F ` y )
                    ( +g ` W )
                    ( ( -g ` W ) ` ( F ` x ) )
                  )
                )
                <
                e
              )
            )
  ) $.
$}

${
  $d C F W X d e y $.

  q1217677-has-right-deriv-at-definition $a |- (
    ( Q1217677HasRightDerivAt W F C X )
    <->
    A. e e. RR+
      E. d e. RR+
        A. y e. ( X (,) ( X + d ) )
          (
            (
              ( norm ` W )
              `
              (
                (
                  ( F ` y )
                  ( +g ` W )
                  ( ( -g ` W ) ` ( F ` X ) )
                )
                ( +g ` W )
                (
                  ( -g ` W )
                  `
                  ( ( y - X ) ( .s ` W ) C )
                )
              )
            )
            <_
            ( e x. ( abs ` ( y - X ) ) )
          )
  ) $.
$}

${
  $d A B C F W u w $.

  thousand-theorems-q1217677-integral-has-strict-deriv-at-of-tendsto-ae-right
    $a |-
    A. W e. { w e. NrmVec | ( Scalar ` w ) = RRfld }
      A. F e. ( ( Base ` W ) ^m RR )
        A. C e. ( Base ` W )
          A. A e. RR
            A. B e. RR
              (
                (
                  W e. CMetSp
                  /\
                  ( Q1217677IntervalIntegrable W F A B )
                  /\
                  ( Q1217677StronglyMeasurableAt W F B )
                  /\
                  ( Q1217677AETendstoAt W F B C )
                )
                ->
                (
                  Q1217677HasStrictDerivAt
                  W
                  ( u e. RR |-> ( Q1217677Integral W F A u ) )
                  C
                  B
                )
              )
  $.
$}

${
  $d A B F G W w x $.

  thousand-theorems-q1217677-integral-eq-sub-of-has-deriv-right-of-le
    $a |-
    A. W e. { w e. NrmVec | ( Scalar ` w ) = RRfld }
      A. F e. ( ( Base ` W ) ^m RR )
        A. G e. ( ( Base ` W ) ^m RR )
          A. A e. RR
            A. B e. RR
              (
                (
                  W e. CMetSp
                  /\
                  A <_ B
                  /\
                  (
                    Q1217677ContinuousOn
                    W
                    F
                    ( A [,] B )
                  )
                  /\
                  A. x e. ( A (,) B )
                    (
                      Q1217677HasRightDerivAt
                      W
                      F
                      ( G ` x )
                      x
                    )
                  /\
                  ( Q1217677IntervalIntegrable W G A B )
                )
                ->
                (
                  Q1217677Integral W G A B
                )
                =
                (
                  ( F ` B )
                  ( +g ` W )
                  ( ( -g ` W ) ` ( F ` A ) )
                )
              )
  $.
$}
