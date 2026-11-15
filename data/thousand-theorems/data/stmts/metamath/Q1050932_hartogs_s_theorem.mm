$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1050932
  (thousand-theorems__metamath__Q1050932), "Hartogs's theorem": a function
  from the complex plane squared to a complete second-countable complex
  normed space that is analytic separately in each coordinate on an open set
  is jointly analytic there. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1050932Sub is subtraction in the codomain normed vector space.
  Q1050932PairDist is the l1 distance on CC X. CC; it induces the same
  topology as the product norm used by the Lean source.

  Q1050932HasDeriv0At and Q1050932HasDeriv1At are the complex Frechet
  remainder estimates for the two one-variable slices. Q1050932AnalyticAt0
  and Q1050932AnalyticAt1 require such derivatives throughout a neighborhood
  of the indicated coordinate. Q1050932HasJointDerivAt uses the complex-linear
  map (h0,h1) |-> h0 D0 + h1 D1, which represents every complex-linear map
  from CC squared into E. Q1050932AnalyticAt and Q1050932AnalyticOnNhd are
  their corresponding local joint notions.

  For maps from finite-dimensional complex spaces into a complete complex
  normed space, local complex Frechet differentiability is equivalent to the
  power-series AnalyticAt and AnalyticOnNhd predicates in the Lean source.
  The final $a assertion keeps the complete-space, second-countability,
  openness, separate-analyticity, and joint-analyticity scopes explicit. All
  preceding $a declarations are syntax or faithful definitions; the database
  contains no $p proof statement.
$)

$c Q1050932Sub Q1050932PairDist Q1050932Linear
   Q1050932HasDeriv0At Q1050932HasDeriv1At
   Q1050932AnalyticAt0 Q1050932AnalyticAt1
   Q1050932HasJointDerivAt Q1050932AnalyticAt
   Q1050932AnalyticOnNhd $.

$v D1 $.
q1050932-vD1 $f class D1 $.

q1050932-sub-syntax
  $a class ( Q1050932Sub E x y ) $.
q1050932-pair-dist-syntax
  $a class ( Q1050932PairDist p q ) $.
q1050932-linear-syntax
  $a class ( Q1050932Linear E p q D0 D1 ) $.
q1050932-has-deriv0-at-syntax
  $a wff ( Q1050932HasDeriv0At E F p D0 ) $.
q1050932-has-deriv1-at-syntax
  $a wff ( Q1050932HasDeriv1At E F p D1 ) $.
q1050932-analytic-at0-syntax
  $a wff ( Q1050932AnalyticAt0 E F p ) $.
q1050932-analytic-at1-syntax
  $a wff ( Q1050932AnalyticAt1 E F p ) $.
q1050932-has-joint-deriv-at-syntax
  $a wff ( Q1050932HasJointDerivAt E F p D0 D1 ) $.
q1050932-analytic-at-syntax
  $a wff ( Q1050932AnalyticAt E F p ) $.
q1050932-analytic-on-nhd-syntax
  $a wff ( Q1050932AnalyticOnNhd E F S ) $.

${
  $d E x y $.

  q1050932-sub-definition $a |- (
    Q1050932Sub E x y
  ) = (
    x
    ( +g ` E )
    ( ( -g ` E ) ` y )
  ) $.
$}

${
  $d p q $.

  q1050932-pair-dist-definition $a |- (
    Q1050932PairDist p q
  ) = (
    ( abs ` ( ( 1st ` q ) - ( 1st ` p ) ) )
    +
    ( abs ` ( ( 2nd ` q ) - ( 2nd ` p ) ) )
  ) $.
$}

${
  $d D0 D1 E p q $.

  q1050932-linear-definition $a |- (
    Q1050932Linear E p q D0 D1
  ) = (
    (
      ( ( 1st ` q ) - ( 1st ` p ) )
      ( .s ` E )
      D0
    )
    ( +g ` E )
    (
      ( ( 2nd ` q ) - ( 2nd ` p ) )
      ( .s ` E )
      D1
    )
  ) $.
$}

${
  $d D0 E F d e p z $.

  q1050932-has-deriv0-at-definition $a |- (
    ( Q1050932HasDeriv0At E F p D0 )
    <->
    (
      D0 e. ( Base ` E )
      /\
      A. e e. RR+
        E. d e. RR+
          A. z e. CC
            (
              ( ( abs ` ( z - ( 1st ` p ) ) ) < d )
              ->
              (
                (
                  ( norm ` E )
                  `
                  (
                    Q1050932Sub
                    E
                    (
                      Q1050932Sub
                      E
                      ( F ` <. z , ( 2nd ` p ) >. )
                      ( F ` p )
                    )
                    (
                      ( z - ( 1st ` p ) )
                      ( .s ` E )
                      D0
                    )
                  )
                )
                <_
                (
                  e
                  x.
                  ( abs ` ( z - ( 1st ` p ) ) )
                )
              )
            )
    )
  ) $.
$}

${
  $d D1 E F d e p z $.

  q1050932-has-deriv1-at-definition $a |- (
    ( Q1050932HasDeriv1At E F p D1 )
    <->
    (
      D1 e. ( Base ` E )
      /\
      A. e e. RR+
        E. d e. RR+
          A. z e. CC
            (
              ( ( abs ` ( z - ( 2nd ` p ) ) ) < d )
              ->
              (
                (
                  ( norm ` E )
                  `
                  (
                    Q1050932Sub
                    E
                    (
                      Q1050932Sub
                      E
                      ( F ` <. ( 1st ` p ) , z >. )
                      ( F ` p )
                    )
                    (
                      ( z - ( 2nd ` p ) )
                      ( .s ` E )
                      D1
                    )
                  )
                )
                <_
                (
                  e
                  x.
                  ( abs ` ( z - ( 2nd ` p ) ) )
                )
              )
            )
    )
  ) $.
$}

${
  $d D0 E F p r z $.

  q1050932-analytic-at0-definition $a |- (
    ( Q1050932AnalyticAt0 E F p )
    <->
    E. r e. RR+
      A. z e. CC
        (
          ( ( abs ` ( z - ( 1st ` p ) ) ) < r )
          ->
          E. D0 e. ( Base ` E )
            (
              Q1050932HasDeriv0At
              E F <. z , ( 2nd ` p ) >. D0
            )
        )
  ) $.
$}

${
  $d D1 E F p r z $.

  q1050932-analytic-at1-definition $a |- (
    ( Q1050932AnalyticAt1 E F p )
    <->
    E. r e. RR+
      A. z e. CC
        (
          ( ( abs ` ( z - ( 2nd ` p ) ) ) < r )
          ->
          E. D1 e. ( Base ` E )
            (
              Q1050932HasDeriv1At
              E F <. ( 1st ` p ) , z >. D1
            )
        )
  ) $.
$}

${
  $d D0 D1 E F d e p q $.

  q1050932-has-joint-deriv-at-definition $a |- (
    ( Q1050932HasJointDerivAt E F p D0 D1 )
    <->
    (
      (
        D0 e. ( Base ` E )
        /\
        D1 e. ( Base ` E )
      )
      /\
      A. e e. RR+
        E. d e. RR+
          A. q e. ( CC X. CC )
            (
              ( ( Q1050932PairDist p q ) < d )
              ->
              (
                (
                  ( norm ` E )
                  `
                  (
                    Q1050932Sub
                    E
                    (
                      Q1050932Sub
                      E
                      ( F ` q )
                      ( F ` p )
                    )
                    ( Q1050932Linear E p q D0 D1 )
                  )
                )
                <_
                (
                  e
                  x.
                  ( Q1050932PairDist p q )
                )
              )
            )
    )
  ) $.
$}

${
  $d D0 D1 E F p q r $.

  q1050932-analytic-at-definition $a |- (
    ( Q1050932AnalyticAt E F p )
    <->
    E. r e. RR+
      A. q e. ( CC X. CC )
        (
          ( ( Q1050932PairDist p q ) < r )
          ->
          E. D0 e. ( Base ` E )
            E. D1 e. ( Base ` E )
              (
                Q1050932HasJointDerivAt
                E F q D0 D1
              )
        )
  ) $.
$}

${
  $d E F S p $.

  q1050932-analytic-on-nhd-definition $a |- (
    ( Q1050932AnalyticOnNhd E F S )
    <->
    A. p e. S
      ( Q1050932AnalyticAt E F p )
  ) $.
$}

${
  $d D0 D1 E F S d e p q r v x y z $.

  thousand-theorems-q1050932-hartogs $a |-
    A. E e. { v e. NrmVec | ( Scalar ` v ) = CCfld }
      A. F e. ( ( Base ` E ) ^m ( CC X. CC ) )
        A. S e. ~P ( CC X. CC )
          (
            (
              (
                E e. CMetSp
                /\
                ( TopOpen ` E ) e. 2ndc
              )
              /\
              S e.
                (
                  ( TopOpen ` CCfld )
                  tX
                  ( TopOpen ` CCfld )
                )
              /\
              A. p e. S
                (
                  ( Q1050932AnalyticAt0 E F p )
                  /\
                  ( Q1050932AnalyticAt1 E F p )
                )
            )
            ->
            ( Q1050932AnalyticOnNhd E F S )
          )
  $.
$}
