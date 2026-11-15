$(
  Statement-only formalization of Thousand Theorems corpus artifact Q4378868
  (thousand-theorems__metamath__Q4378868), "Phragmen--Lindelof theorem": a
  complex-differentiable vector-valued function on a horizontal strip,
  continuous on its closure and satisfying the stated double-exponential
  growth and boundary bounds, obeys the same norm bound throughout the
  closed strip. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q4378868OpenStrip is the inverse image under the imaginary-part map of the
  open real interval with endpoints a and b. Q4378868ClosureStrip is its
  actual closure in the standard complex topology; this preserves the Lean
  DiffContOnCl condition even when the interval is empty or degenerate.

  Q4378868ContinuousOn is relative epsilon-delta continuity. Complex
  differentiability within a set is written in the equivalent
  one-dimensional Frechet form: D is the value of the complex-linear
  derivative, so its action on an increment h is h scalar-multiplied by D,
  and the difference quotient estimate ranges over points of that set.
  Q4378868DiffContOnCl combines differentiability within the open strip with
  continuity on its closure.

  Q4378868Growth expands the source filter Big-O condition. It asserts that
  for some c < pi / (b - a), B, nonnegative multiplier A, and real threshold
  R, the norm of F(w) is at most
  A * exp(B * exp(c * |Re(w)|)) whenever w lies in the open strip and
  |Re(w)| >= R. This is exactly eventual domination along the infimum of the
  pullback of atTop by |Re| and the principal filter of the open strip.

  The final unproved $a assertion quantifies over arbitrary SetMM complex
  normed vector spaces and functions on the full complex plane. All preceding
  $a declarations are syntax or faithful definitions; there is no $p proof
  statement.
$)

$c Q4378868Sub Q4378868OpenStrip Q4378868ClosureStrip
   Q4378868ContinuousOn Q4378868HasComplexDerivWithinAt
   Q4378868DifferentiableOn Q4378868DiffContOnCl Q4378868Growth $.

q4378868-sub-syntax $a class ( Q4378868Sub W x y ) $.
q4378868-open-strip-syntax $a class ( Q4378868OpenStrip a b ) $.
q4378868-closure-strip-syntax $a class ( Q4378868ClosureStrip a b ) $.
q4378868-continuous-on-syntax
  $a wff ( Q4378868ContinuousOn W F S ) $.
q4378868-has-complex-deriv-within-at-syntax
  $a wff ( Q4378868HasComplexDerivWithinAt W F S x D ) $.
q4378868-differentiable-on-syntax
  $a wff ( Q4378868DifferentiableOn W F S ) $.
q4378868-diff-cont-on-cl-syntax
  $a wff ( Q4378868DiffContOnCl W F a b ) $.
q4378868-growth-syntax
  $a wff ( Q4378868Growth W F a b ) $.

${
  $d W x y $.

  q4378868-sub-definition $a |- (
    Q4378868Sub W x y
  ) = (
    x
    ( +g ` W )
    ( ( -g ` W ) ` y )
  ) $.
$}

${
  $d a b w $.

  q4378868-open-strip-definition $a |- (
    Q4378868OpenStrip a b
  ) = {
    w e. CC |
      (
        a < ( Im ` w )
        /\
        ( Im ` w ) < b
      )
  } $.
$}

${
  $d a b $.

  q4378868-closure-strip-definition $a |- (
    Q4378868ClosureStrip a b
  ) = (
    ( cls ` ( TopOpen ` CCfld ) )
    `
    ( Q4378868OpenStrip a b )
  ) $.
$}

${
  $d F S W d e x y $.

  q4378868-continuous-on-definition $a |- (
    ( Q4378868ContinuousOn W F S )
    <->
    A. x e. S
      A. e e. RR+
        E. d e. RR+
          A. y e. S
            (
              ( ( abs ` ( y - x ) ) < d )
              ->
              (
                (
                  ( norm ` W )
                  `
                  ( Q4378868Sub W ( F ` y ) ( F ` x ) )
                )
                <
                e
              )
            )
  ) $.
$}

${
  $d D F S W d e x y $.

  q4378868-has-complex-deriv-within-at-definition $a |- (
    ( Q4378868HasComplexDerivWithinAt W F S x D )
    <->
    (
      D e. ( Base ` W )
      /\
      A. e e. RR+
        E. d e. RR+
          A. y e. S
            (
              ( ( abs ` ( y - x ) ) < d )
              ->
              (
                (
                  ( norm ` W )
                  `
                  (
                    Q4378868Sub
                    W
                    ( Q4378868Sub W ( F ` y ) ( F ` x ) )
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
  $d D F S W x $.

  q4378868-differentiable-on-definition $a |- (
    ( Q4378868DifferentiableOn W F S )
    <->
    A. x e. S
      E. D e. ( Base ` W )
        ( Q4378868HasComplexDerivWithinAt W F S x D )
  ) $.
$}

${
  $d F W a b $.

  q4378868-diff-cont-on-cl-definition $a |- (
    ( Q4378868DiffContOnCl W F a b )
    <->
    (
      (
        Q4378868DifferentiableOn
        W F ( Q4378868OpenStrip a b )
      )
      /\
      (
        Q4378868ContinuousOn
        W F ( Q4378868ClosureStrip a b )
      )
    )
  ) $.
$}

${
  $d A B F R W a b c w $.

  q4378868-growth-definition $a |- (
    ( Q4378868Growth W F a b )
    <->
    E. c e. RR
      (
        c < ( _pi / ( b - a ) )
        /\
        E. B e. RR
          E. A e. ( 0 [,) +oo )
            E. R e. RR
              A. w e. ( Q4378868OpenStrip a b )
                (
                  R <_ ( abs ` ( Re ` w ) )
                  ->
                  (
                    ( norm ` W )
                    `
                    ( F ` w )
                  )
                  <_
                  (
                    A
                    x.
                    (
                      exp
                      `
                      (
                        B
                        x.
                        (
                          exp
                          `
                          (
                            c
                            x.
                            ( abs ` ( Re ` w ) )
                          )
                        )
                      )
                    )
                  )
                )
      )
  ) $.
$}

${
  $d C F W a b w z $.

  thousand-theorems-q4378868-phragmen-lindelof-horizontal-strip $a |-
    A. W e. { v e. NrmVec | ( Scalar ` v ) = CCfld }
      A. F e. ( ( Base ` W ) ^m CC )
        A. a e. RR
          A. b e. RR
            A. C e. RR
              A. z e. CC
                (
                  (
                    ( Q4378868DiffContOnCl W F a b )
                    /\
                    ( Q4378868Growth W F a b )
                    /\
                    A. w e. CC
                      (
                        ( Im ` w ) = a
                        ->
                        (
                          ( ( norm ` W ) ` ( F ` w ) )
                          <_
                          C
                        )
                      )
                    /\
                    A. w e. CC
                      (
                        ( Im ` w ) = b
                        ->
                        (
                          ( ( norm ` W ) ` ( F ` w ) )
                          <_
                          C
                        )
                      )
                    /\
                    a <_ ( Im ` z )
                    /\
                    ( Im ` z ) <_ b
                  )
                  ->
                  (
                    ( ( norm ` W ) ` ( F ` z ) )
                    <_
                    C
                  )
                )
  $.
$}
