$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3229335
  (thousand-theorems__metamath__Q3229335), "Borel-Caratheodory theorem":
  if 0 < M and 0 < R, a complex function differentiable on the open ball
  of radius R about zero and mapping that ball into the half-plane Re(w) <= M
  satisfies the canonical two-term norm bound at every point of the ball.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The complete canonical source proposition has arbitrary f : CC -> CC,
  M R : RR, and z : CC. Its five hypotheses are, in order, 0 < M;
  complex differentiability of f on ball(0,R); MapsTo f ball(0,R)
  { w | Re(w) <= M }; 0 < R; and z in ball(0,R). Its conclusion is

    |f(z)| <= 2*M*|z|/(R-|z|)
              + |f(0)|*(R+|z|)/(R-|z|).

  Q3229335Ball is exactly ball(0,R), the open complex ball centered at zero.
  Q3229335HasComplexDerivWithinAt is the epsilon-delta Frechet derivative
  condition within a set; in one complex dimension the derivative acts on an
  increment by complex multiplication. Q3229335DifferentiableOn quantifies
  such a derivative at every point of the ball. Q3229335RealPartBound is
  exactly the displayed MapsTo condition.

  The final unproved $a assertion quantifies over arbitrary total functions
  from CC to CC, real M and R, and complex z. Every preceding $a declaration
  is syntax or an explicit faithful definition; this database has no $p proof
  statement.
$)

$c Q3229335Ball Q3229335HasComplexDerivWithinAt
   Q3229335DifferentiableOn Q3229335RealPartBound $.

q3229335-ball-syntax
  $a class ( Q3229335Ball R ) $.
q3229335-has-complex-deriv-within-at-syntax
  $a wff ( Q3229335HasComplexDerivWithinAt F S x D ) $.
q3229335-differentiable-on-syntax
  $a wff ( Q3229335DifferentiableOn F S ) $.
q3229335-real-part-bound-syntax
  $a wff ( Q3229335RealPartBound F R M ) $.

${
  $d R x $.

  q3229335-ball-definition $a |- (
    Q3229335Ball R
  ) = {
    x e. CC |
      ( abs ` x ) < R
  } $.
$}

${
  $d D F S d e x y $.

  q3229335-has-complex-deriv-within-at-definition $a |- (
    ( Q3229335HasComplexDerivWithinAt F S x D )
    <->
    (
      D e. CC
      /\
      A. e e. RR+
        E. d e. RR+
          A. y e. S
            (
              ( ( abs ` ( y - x ) ) < d )
              ->
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
                  (
                    ( y - x )
                    x.
                    D
                  )
                )
              )
              <_
              (
                e
                x.
                ( abs ` ( y - x ) )
              )
            )
    )
  ) $.
$}

${
  $d F S d x $.

  q3229335-differentiable-on-definition $a |- (
    ( Q3229335DifferentiableOn F S )
    <->
    A. x e. S
      E. d e. CC
        ( Q3229335HasComplexDerivWithinAt F S x d )
  ) $.
$}

${
  $d F M R x $.

  q3229335-real-part-bound-definition $a |- (
    ( Q3229335RealPartBound F R M )
    <->
    A. x e. ( Q3229335Ball R )
      ( Re ` ( F ` x ) ) <_ M
  ) $.
$}

${
  $d f m r z $.

  thousand-theorems-q3229335-borel-caratheodory $a |-
    A. f e. ( CC ^m CC )
      A. m e. RR
        A. r e. RR
          A. z e. CC
            (
              (
                0 < m
                /\
                (
                  ( Q3229335DifferentiableOn
                    f
                    ( Q3229335Ball r )
                  )
                  /\
                  (
                    ( Q3229335RealPartBound f r m )
                    /\
                    (
                      0 < r
                      /\
                      z e. ( Q3229335Ball r )
                    )
                  )
                )
              )
              ->
              (
                ( abs ` ( f ` z ) )
                <_
                (
                  (
                    (
                      ( 2 x. m )
                      x.
                      ( abs ` z )
                    )
                    /
                    (
                      r
                      -
                      ( abs ` z )
                    )
                  )
                  +
                  (
                    (
                      ( abs ` ( f ` 0 ) )
                      x.
                      (
                        r
                        +
                        ( abs ` z )
                      )
                    )
                    /
                    (
                      r
                      -
                      ( abs ` z )
                    )
                  )
                )
              )
            )
  $.
$}
