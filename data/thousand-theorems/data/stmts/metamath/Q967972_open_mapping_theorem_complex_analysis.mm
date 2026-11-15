$(
  Statement-only formalization of Thousand Theorems corpus artifact Q967972
  (thousand-theorems__metamath__Q967972), "Open mapping theorem (complex
  analysis)": a complex-valued function analytic on neighborhoods of a
  preconnected subset of an arbitrary complex normed vector space is either
  constant on that subset or maps every open subset of it to an open subset
  of the complex plane. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q967972Sub is subtraction in the domain normed vector space, and
  Q967972OpenBall is its norm-open ball. Q967972ContinuousLinear gives an
  algebraic complex-linear map together with a global operator bound.
  Q967972HasFDerivAt is the epsilon-delta Frechet remainder estimate.

  Q967972AnalyticOnNhd says that every point of U has a positive-radius
  neighborhood on which F is complex Frechet differentiable. For maps from
  an arbitrary complex normed vector space to the complete complex field,
  local complex Frechet differentiability is equivalent to the
  AnalyticOnNhd power-series formulation in the Lean source.

  Preconnectedness is rendered as connectedness of the subspace topology.
  The final $a assertion preserves the source alternative verbatim at the
  set-theoretic level: either one complex value is taken throughout U, or
  every ambient-open subset S of U has ambient-open image F " S. All $a
  declarations before the final assertion are syntax or explicit faithful
  definitions; the database contains no $p proof statement.
$)

$c Q967972Sub Q967972OpenBall Q967972ContinuousLinear
   Q967972HasFDerivAt Q967972AnalyticOnNhd $.

q967972-sub-syntax $a class ( Q967972Sub V x y ) $.
q967972-open-ball-syntax $a class ( Q967972OpenBall V x r ) $.
q967972-continuous-linear-syntax
  $a wff ( Q967972ContinuousLinear V L ) $.
q967972-has-fderiv-at-syntax
  $a wff ( Q967972HasFDerivAt V F x L ) $.
q967972-analytic-on-nhd-syntax
  $a wff ( Q967972AnalyticOnNhd V F U ) $.

${
  $d V x y $.

  q967972-sub-definition $a |- (
    Q967972Sub V x y
  ) = (
    x
    ( +g ` V )
    ( ( -g ` V ) ` y )
  ) $.
$}

${
  $d V r x y $.

  q967972-open-ball-definition $a |- (
    Q967972OpenBall V x r
  ) = {
    y e. ( Base ` V ) |
      (
        ( ( norm ` V ) ` ( Q967972Sub V y x ) )
        <
        r
      )
  } $.
$}

${
  $d C L V u $.

  q967972-continuous-linear-definition $a |- (
    ( Q967972ContinuousLinear V L )
    <->
    (
      L e. ( V LMHom ( ringLMod ` CCfld ) )
      /\
      E. C e. ( 0 [,) +oo )
        A. u e. ( Base ` V )
          (
            ( abs ` ( L ` u ) )
            <_
            (
              C
              x.
              ( ( norm ` V ) ` u )
            )
          )
    )
  ) $.
$}

${
  $d F L V d e x y $.

  q967972-has-fderiv-at-definition $a |- (
    ( Q967972HasFDerivAt V F x L )
    <->
    A. e e. RR+
      E. d e. RR+
        A. y e. ( Base ` V )
          (
            (
              ( ( norm ` V ) ` ( Q967972Sub V y x ) )
              <
              d
            )
            ->
            (
              (
                abs
                `
                (
                  (
                    ( F ` y )
                    -
                    ( F ` x )
                  )
                  -
                  ( L ` ( Q967972Sub V y x ) )
                )
              )
              <_
              (
                e
                x.
                ( ( norm ` V ) ` ( Q967972Sub V y x ) )
              )
            )
          )
  ) $.
$}

${
  $d F L U V r x y $.

  q967972-analytic-on-nhd-definition $a |- (
    ( Q967972AnalyticOnNhd V F U )
    <->
    A. x e. U
      E. r e. RR+
        A. y e. ( Q967972OpenBall V x r )
          E. L
            (
              ( Q967972ContinuousLinear V L )
              /\
              ( Q967972HasFDerivAt V F y L )
            )
  ) $.
$}

${
  $d F S U V v w z $.

  thousand-theorems-q967972-open-mapping-theorem $a |-
    A. V e. { v e. NrmVec | ( Scalar ` v ) = CCfld }
      A. F e. ( CC ^m ( Base ` V ) )
        A. U e. ~P ( Base ` V )
          (
            (
              ( Q967972AnalyticOnNhd V F U )
              /\
              ( ( TopOpen ` V ) |`t U ) e. Conn
            )
            ->
            (
              E. w e. CC
                A. z e. U
                  ( F ` z ) = w
              \/
              A. S e. ~P ( Base ` V )
                (
                  S C_ U
                  ->
                  (
                    S e. ( TopOpen ` V )
                    ->
                    ( F " S ) e. ( TopOpen ` CCfld )
                  )
                )
            )
          )
  $.
$}
