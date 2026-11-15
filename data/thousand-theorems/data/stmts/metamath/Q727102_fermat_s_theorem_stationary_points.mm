$(
  Statement-only formalization of Thousand Theorems corpus artifact Q727102
  (thousand-theorems__metamath__Q727102), "Fermat's theorem (stationary
  points)": the totalized Frechet derivative of a real-valued function on an
  arbitrary real normed vector space, and the totalized ordinary derivative
  of a real function, vanish at every local extremum. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  Q727102LocalExtr expands IsLocalExtr using a positive norm-ball radius.
  Q727102ContinuousLinear represents a bounded real-linear functional as its
  underlying total function, and Q727102HasFDerivAt is the epsilon-delta
  Frechet remainder estimate.

  Q727102FDeriv selects the unique Frechet derivative when it exists and is
  unique, and otherwise returns the zero function. Equality with the displayed
  zero function is therefore extensionally equivalent to Mathlib's equality
  of continuous linear maps. Q727102LocalExtrReal is the scalar specialization,
  while Q727102Deriv totalizes SetMM's partial real derivative by returning
  zero where no derivative exists. These totalizations exactly match the
  source fderiv and deriv conventions.

  The two final $a declarations are the indexed unproved corpus statements.
  Every preceding $a declaration is syntax or an explicit definition, and
  this database contains no $p proof statement.
$)

$c Q727102Sub Q727102LocalExtr Q727102ContinuousLinear
   Q727102HasFDerivAt Q727102FDeriv Q727102LocalExtrReal
   Q727102Deriv $.

q727102-sub-syntax $a class ( Q727102Sub V x y ) $.
q727102-local-extr-syntax
  $a wff ( Q727102LocalExtr V F A ) $.
q727102-continuous-linear-syntax
  $a wff ( Q727102ContinuousLinear V L ) $.
q727102-has-fderiv-at-syntax
  $a wff ( Q727102HasFDerivAt V F A L ) $.
q727102-fderiv-syntax
  $a class ( Q727102FDeriv V F A ) $.
q727102-local-extr-real-syntax
  $a wff ( Q727102LocalExtrReal F A ) $.
q727102-deriv-syntax
  $a class ( Q727102Deriv F A ) $.

${
  $d V x y $.

  q727102-sub-definition $a |- (
    Q727102Sub V x y
  ) = (
    x
    ( +g ` V )
    ( ( -g ` V ) ` y )
  ) $.
$}

${
  $d A F V d y $.

  q727102-local-extr-definition $a |- (
    ( Q727102LocalExtr V F A )
    <->
    (
      (
        F e. ( RR ^m ( Base ` V ) )
        /\
        A e. ( Base ` V )
      )
      /\
      (
        E. d e. RR+
          A. y e. ( Base ` V )
            (
              (
                ( norm ` V )
                `
                ( Q727102Sub V y A )
              )
              <
              d
              ->
              ( F ` A ) <_ ( F ` y )
            )
        \/
        E. d e. RR+
          A. y e. ( Base ` V )
            (
              (
                ( norm ` V )
                `
                ( Q727102Sub V y A )
              )
              <
              d
              ->
              ( F ` y ) <_ ( F ` A )
            )
      )
    )
  ) $.
$}

${
  $d C L V r u v $.

  q727102-continuous-linear-definition $a |- (
    ( Q727102ContinuousLinear V L )
    <->
    (
      L e. ( RR ^m ( Base ` V ) )
      /\
      (
        A. u e. ( Base ` V )
          A. v e. ( Base ` V )
            (
              L
              `
              (
                u
                ( +g ` V )
                v
              )
            )
            =
            (
              ( L ` u )
              +
              ( L ` v )
            )
        /\
        A. r e. RR
          A. u e. ( Base ` V )
            (
              L
              `
              (
                r
                ( .s ` V )
                u
              )
            )
            =
            (
              r
              x.
              ( L ` u )
            )
        /\
        E. C e. ( 0 [,) +oo )
          A. u e. ( Base ` V )
            (
              abs
              `
              ( L ` u )
            )
            <_
            (
              C
              x.
              (
                ( norm ` V )
                `
                u
              )
            )
      )
    )
  ) $.
$}

${
  $d A F L V d e y $.

  q727102-has-fderiv-at-definition $a |- (
    ( Q727102HasFDerivAt V F A L )
    <->
    (
      (
        F e. ( RR ^m ( Base ` V ) )
        /\
        A e. ( Base ` V )
        /\
        ( Q727102ContinuousLinear V L )
      )
      /\
      A. e e. RR+
        E. d e. RR+
          A. y e. ( Base ` V )
            (
              (
                (
                  ( norm ` V )
                  `
                  ( Q727102Sub V y A )
                )
                <
                d
              )
              ->
              (
                abs
                `
                (
                  (
                    ( F ` y )
                    -
                    ( F ` A )
                  )
                  -
                  (
                    L
                    `
                    ( Q727102Sub V y A )
                  )
                )
              )
              <_
              (
                e
                x.
                (
                  ( norm ` V )
                  `
                  ( Q727102Sub V y A )
                )
              )
            )
    )
  ) $.
$}

${
  $d A F L V u $.

  q727102-fderiv-definition $a |- (
    Q727102FDeriv V F A
  ) =
    if
    (
      E! L e. ( RR ^m ( Base ` V ) )
        ( Q727102HasFDerivAt V F A L ) ,
      (
        iota_ L e. ( RR ^m ( Base ` V ) )
          ( Q727102HasFDerivAt V F A L )
      ) ,
      (
        u e. ( Base ` V )
          |->
          0
      )
    )
  $.
$}

${
  $d A F d y $.

  q727102-local-extr-real-definition $a |- (
    ( Q727102LocalExtrReal F A )
    <->
    (
      (
        F e. ( RR ^m RR )
        /\
        A e. RR
      )
      /\
      (
        E. d e. RR+
          A. y e. RR
            (
              ( abs ` ( y - A ) ) < d
              ->
              ( F ` A ) <_ ( F ` y )
            )
        \/
        E. d e. RR+
          A. y e. RR
            (
              ( abs ` ( y - A ) ) < d
              ->
              ( F ` y ) <_ ( F ` A )
            )
      )
    )
  ) $.
$}

${
  $d A F $.

  q727102-deriv-definition $a |- (
    Q727102Deriv F A
  ) =
    if
    (
      A e. dom ( RR _D F ) ,
      ( ( RR _D F ) ` A ) ,
      0
    )
  $.
$}

${
  $d A F V u v $.

  thousand-theorems-q727102-is-local-extr-fderiv-eq-zero $a |-
    A. V e. { v e. NrmVec | ( Scalar ` v ) = RRfld }
      A. F e. ( RR ^m ( Base ` V ) )
        A. A e. ( Base ` V )
          (
            ( Q727102LocalExtr V F A )
            ->
            (
              Q727102FDeriv V F A
            )
            =
            (
              u e. ( Base ` V )
                |->
                0
            )
          )
  $.
$}

${
  $d A F $.

  thousand-theorems-q727102-is-local-extr-deriv-eq-zero $a |-
    A. F e. ( RR ^m RR )
      A. A e. RR
        (
          ( Q727102LocalExtrReal F A )
          ->
          ( Q727102Deriv F A ) = 0
        )
  $.
$}
