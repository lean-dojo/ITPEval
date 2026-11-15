$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1140119
  (thousand-theorems__metamath__Q1140119), "Morera's theorem": for a function
  from the complex numbers to an arbitrary complete complex normed vector
  space on an open set, vanishing oriented integrals around every
  axis-parallel rectangle together with continuity is equivalent to complex
  differentiability on that set. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1140119Rectangle is the closed axis-parallel rectangle with opposite
  corners z and w. Q1140119FunctionIntegrable encodes almost-everywhere
  strong measurability and finite L1 norm. Q1140119HasIntegral defines the
  Banach-valued Bochner integral by L1-approximation with measurable
  finite-range functions, and Q1140119Integral is its directed totalization.
  Q1140119WedgeIntegral is exactly the source wedge integral: first along the
  horizontal segment from z to w.re + z.im*i, then along the vertical segment
  to w.

  Q1140119ConservativeOn states that for every rectangle contained in U, the
  wedge integral from z to w is the negative of the reverse wedge integral.
  Q1140119ContinuousOn is relative epsilon-delta continuity.
  Q1140119HasComplexDerivWithinAt uses the equivalent one-dimensional
  complex Frechet remainder estimate, and Q1140119DifferentiableOn
  existentially quantifies that derivative at every point of U.

  The final unproved $a assertion quantifies over arbitrary complete SetMM
  complex normed vector spaces, total functions on CC, and open subsets of
  CC. Every preceding $a declaration is syntax or an explicit faithful
  definition; this root artifact has no $p proof statement.
$)

$c Q1140119Sub Q1140119Restrict Q1140119Tendsto Q1140119AEStrong
   Q1140119Simple Q1140119SimpleIntegral Q1140119LIntegral
   Q1140119Diff Q1140119L1Distance Q1140119FunctionIntegrable
   Q1140119HasIntegral Q1140119TotalIntegral Q1140119Integral
   Q1140119Rectangle Q1140119WedgeIntegral Q1140119ConservativeOn
   Q1140119ContinuousOn Q1140119HasComplexDerivWithinAt
   Q1140119DifferentiableOn $.

q1140119-sub-syntax
  $a class ( Q1140119Sub W x y ) $.
q1140119-restrict-syntax
  $a class ( Q1140119Restrict W H A B ) $.
q1140119-tendsto-syntax
  $a wff ( Q1140119Tendsto W S C ) $.
q1140119-aestrong-syntax
  $a wff ( Q1140119AEStrong M W H ) $.
q1140119-simple-syntax
  $a wff ( Q1140119Simple M G ) $.
q1140119-simple-integral-syntax
  $a class ( Q1140119SimpleIntegral M G ) $.
q1140119-lintegral-syntax
  $a class ( Q1140119LIntegral M H ) $.
q1140119-diff-syntax
  $a class ( Q1140119Diff M W H K ) $.
q1140119-l1-distance-syntax
  $a class ( Q1140119L1Distance M W H K ) $.
q1140119-function-integrable-syntax
  $a wff ( Q1140119FunctionIntegrable M W H ) $.
q1140119-has-integral-syntax
  $a wff ( Q1140119HasIntegral M W H y ) $.
q1140119-total-integral-syntax
  $a class ( Q1140119TotalIntegral W H ) $.
q1140119-integral-syntax
  $a class ( Q1140119Integral W H A B ) $.
q1140119-rectangle-syntax
  $a class ( Q1140119Rectangle z w ) $.
q1140119-wedge-integral-syntax
  $a class ( Q1140119WedgeIntegral W F z w ) $.
q1140119-conservative-on-syntax
  $a wff ( Q1140119ConservativeOn W F U ) $.
q1140119-continuous-on-syntax
  $a wff ( Q1140119ContinuousOn W F U ) $.
q1140119-has-complex-deriv-within-at-syntax
  $a wff ( Q1140119HasComplexDerivWithinAt W F U x D ) $.
q1140119-differentiable-on-syntax
  $a wff ( Q1140119DifferentiableOn W F U ) $.

${
  $d W x y $.

  q1140119-sub-definition $a |- (
    Q1140119Sub W x y
  ) = (
    x
    ( +g ` W )
    ( ( -g ` W ) ` y )
  ) $.
$}

${
  $d A B H W t $.

  q1140119-restrict-definition $a |- (
    Q1140119Restrict W H A B
  ) = (
    t e. RR |->
    if (
      t e. ( A (,) B ) ,
      ( H ` t ) ,
      ( 0g ` W )
    )
  ) $.
$}

${
  $d C S W $.

  q1140119-tendsto-definition $a |- (
    ( Q1140119Tendsto W S C )
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

  q1140119-aestrong-definition $a |- (
    ( Q1140119AEStrong M W H )
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
                  Q1140119Tendsto
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

  q1140119-simple-definition $a |- (
    ( Q1140119Simple M G )
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

  q1140119-simple-integral-definition $a |- (
    Q1140119SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q1140119-lintegral-definition $a |- (
    Q1140119LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q1140119Simple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q1140119SimpleIntegral M G )
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

  q1140119-diff-definition $a |- (
    Q1140119Diff M W H K
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

  q1140119-l1-distance-definition $a |- (
    Q1140119L1Distance M W H K
  ) =
    (
      Q1140119LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q1140119Diff M W H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M W x $.

  q1140119-function-integrable-definition $a |- (
    ( Q1140119FunctionIntegrable M W H )
    <->
    (
      ( Q1140119AEStrong M W H )
      /\
      (
        Q1140119LIntegral
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

  q1140119-has-integral-definition $a |- (
    ( Q1140119HasIntegral M W H y )
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
            Q1140119Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q1140119L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q1140119Tendsto
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

  q1140119-total-integral-definition $a |- (
    Q1140119TotalIntegral W H
  ) = if (
    (
      W e. CMetSp
      /\
      ( Q1140119FunctionIntegrable vol W H )
    ) ,
    (
      iota_ y e. ( Base ` W )
        ( Q1140119HasIntegral vol W H y )
    ) ,
    ( 0g ` W )
  ) $.
$}

${
  $d A B H W $.

  q1140119-integral-definition $a |- (
    Q1140119Integral W H A B
  ) = if (
    A <_ B ,
    (
      Q1140119TotalIntegral
      W
      ( Q1140119Restrict W H A B )
    ) ,
    (
      ( -g ` W )
      `
      (
        Q1140119TotalIntegral
        W
        ( Q1140119Restrict W H B A )
      )
    )
  ) $.
$}

${
  $d u w z $.

  q1140119-rectangle-definition $a |- (
    Q1140119Rectangle z w
  ) = {
    u e. CC |
      (
        (
          (
            ( Re ` z ) <_ ( Re ` u )
            /\
            ( Re ` u ) <_ ( Re ` w )
          )
          \/
          (
            ( Re ` w ) <_ ( Re ` u )
            /\
            ( Re ` u ) <_ ( Re ` z )
          )
        )
        /\
        (
          (
            ( Im ` z ) <_ ( Im ` u )
            /\
            ( Im ` u ) <_ ( Im ` w )
          )
          \/
          (
            ( Im ` w ) <_ ( Im ` u )
            /\
            ( Im ` u ) <_ ( Im ` z )
          )
        )
      )
  } $.
$}

${
  $d F W t w x y z $.

  q1140119-wedge-integral-definition $a |- (
    Q1140119WedgeIntegral W F z w
  ) = (
    (
      Q1140119Integral
      W
      (
        x e. RR |->
        (
          F
          `
          (
            x
            +
            ( ( Im ` z ) x. _i )
          )
        )
      )
      ( Re ` z )
      ( Re ` w )
    )
    ( +g ` W )
    (
      _i
      ( .s ` W )
      (
        Q1140119Integral
        W
        (
          y e. RR |->
          (
            F
            `
            (
              ( Re ` w )
              +
              ( y x. _i )
            )
          )
        )
        ( Im ` z )
        ( Im ` w )
      )
    )
  ) $.
$}

${
  $d F U W w z $.

  q1140119-conservative-on-definition $a |- (
    ( Q1140119ConservativeOn W F U )
    <->
    A. z e. CC
      A. w e. CC
        (
          ( Q1140119Rectangle z w ) C_ U
          ->
          (
            Q1140119WedgeIntegral W F z w
          )
          =
          (
            ( -g ` W )
            `
            ( Q1140119WedgeIntegral W F w z )
          )
        )
  ) $.
$}

${
  $d F U W d e x y $.

  q1140119-continuous-on-definition $a |- (
    ( Q1140119ContinuousOn W F U )
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
                  ( Q1140119Sub W ( F ` y ) ( F ` x ) )
                )
                <
                e
              )
            )
  ) $.
$}

${
  $d D F U W d e x y $.

  q1140119-has-complex-deriv-within-at-definition $a |- (
    ( Q1140119HasComplexDerivWithinAt W F U x D )
    <->
    (
      D e. ( Base ` W )
      /\
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
                    Q1140119Sub
                    W
                    ( Q1140119Sub W ( F ` y ) ( F ` x ) )
                    ( ( y - x ) ( .s ` W ) D )
                  )
                )
                <_
                ( e x. ( abs ` ( y - x ) ) )
              )
            )
    )
  ) $.
$}

${
  $d D F U W x $.

  q1140119-differentiable-on-definition $a |- (
    ( Q1140119DifferentiableOn W F U )
    <->
    A. x e. U
      E. D e. ( Base ` W )
        ( Q1140119HasComplexDerivWithinAt W F U x D )
  ) $.
$}

${
  $d F U W v $.

  thousand-theorems-q1140119-morera $a |-
    A. W e. { v e. NrmVec | ( Scalar ` v ) = CCfld }
      A. F e. ( ( Base ` W ) ^m CC )
        A. U e. ~P CC
          (
            (
              W e. CMetSp
              /\
              U e. ( TopOpen ` CCfld )
            )
            ->
            (
              (
                ( Q1140119ConservativeOn W F U )
                /\
                ( Q1140119ContinuousOn W F U )
              )
              <->
              ( Q1140119DifferentiableOn W F U )
            )
          )
  $.
$}
