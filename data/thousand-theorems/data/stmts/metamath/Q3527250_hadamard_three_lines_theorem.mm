$(
  Statement-only formalization of Thousand Theorems corpus artifact Q3527250
  (thousand-theorems__metamath__Q3527250), "Hadamard three-lines theorem":
  a bounded complex-differentiable vector-valued function on a vertical strip,
  continuous on its closure, is bounded at each point by the interpolated
  supremum norms on the two boundary lines. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q3527250OpenStrip and Q3527250ClosedStrip are the inverse images under the
  real-part map of the open and closed real intervals with endpoints l and u.
  Q3527250ClosureStrip is the actual topological closure of the open strip.

  Q3527250ContinuousOn is relative epsilon-delta continuity.
  Q3527250HasComplexDerivWithinAt is the one-dimensional Frechet definition
  within a set: D is the value of the complex-linear derivative, so its action
  on an increment h is h scalar-multiplied by D. Q3527250DiffContOnCl combines
  differentiability within the open strip with continuity on its closure.
  Under the theorem's assumption l < u, that closure is exactly
  Q3527250ClosedStrip.

  Q3527250SupNormIm is the real supremum of the norms of F on the complete
  vertical line with fixed real part. Q3527250Interp is exactly the source
  interpStrip' definition: it is zero if either boundary supremum is zero,
  and otherwise uses SetMM's complex-power operation with the normalized
  complex strip coordinate.

  The final unproved $a assertion quantifies over arbitrary SetMM complex
  normed vector spaces and functions on the full complex plane. Its preceding
  $a declarations are syntax or faithful definitions only; there is no $p
  proof statement.
$)

$c Q3527250Sub Q3527250OpenStrip Q3527250ClosedStrip
   Q3527250ClosureStrip
   Q3527250ContinuousOn Q3527250HasComplexDerivWithinAt
   Q3527250DifferentiableOn Q3527250DiffContOnCl Q3527250BddAbove
   Q3527250SupNormIm Q3527250Interp $.

q3527250-sub-syntax $a class ( Q3527250Sub W x y ) $.
q3527250-open-strip-syntax $a class ( Q3527250OpenStrip l u ) $.
q3527250-closed-strip-syntax $a class ( Q3527250ClosedStrip l u ) $.
q3527250-closure-strip-syntax $a class ( Q3527250ClosureStrip l u ) $.
q3527250-continuous-on-syntax
  $a wff ( Q3527250ContinuousOn W F S ) $.
q3527250-has-complex-deriv-within-at-syntax
  $a wff ( Q3527250HasComplexDerivWithinAt W F S x D ) $.
q3527250-differentiable-on-syntax
  $a wff ( Q3527250DifferentiableOn W F S ) $.
q3527250-diff-cont-on-cl-syntax
  $a wff ( Q3527250DiffContOnCl W F l u ) $.
q3527250-bdd-above-syntax
  $a wff ( Q3527250BddAbove W F S ) $.
q3527250-ssup-norm-im-syntax
  $a class ( Q3527250SupNormIm W F x ) $.
q3527250-interp-syntax
  $a class ( Q3527250Interp W F l u z ) $.

${
  $d W x y $.

  q3527250-sub-definition $a |- (
    Q3527250Sub W x y
  ) = (
    x
    ( +g ` W )
    ( ( -g ` W ) ` y )
  ) $.
$}

${
  $d l u z $.

  q3527250-open-strip-definition $a |- (
    Q3527250OpenStrip l u
  ) = {
    z e. CC |
      (
        l < ( Re ` z )
        /\
        ( Re ` z ) < u
      )
  } $.
$}

${
  $d l u z $.

  q3527250-closed-strip-definition $a |- (
    Q3527250ClosedStrip l u
  ) = {
    z e. CC |
      (
        l <_ ( Re ` z )
        /\
        ( Re ` z ) <_ u
      )
  } $.
$}

${
  $d l u $.

  q3527250-closure-strip-definition $a |- (
    Q3527250ClosureStrip l u
  ) = (
    ( cls ` ( TopOpen ` CCfld ) )
    `
    ( Q3527250OpenStrip l u )
  ) $.
$}

${
  $d F S W d e x y $.

  q3527250-continuous-on-definition $a |- (
    ( Q3527250ContinuousOn W F S )
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
                  ( Q3527250Sub W ( F ` y ) ( F ` x ) )
                )
                <
                e
              )
            )
  ) $.
$}

${
  $d D F S W d e x y $.

  q3527250-has-complex-deriv-within-at-definition $a |- (
    ( Q3527250HasComplexDerivWithinAt W F S x D )
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
                    Q3527250Sub
                    W
                    ( Q3527250Sub W ( F ` y ) ( F ` x ) )
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

  q3527250-differentiable-on-definition $a |- (
    ( Q3527250DifferentiableOn W F S )
    <->
    A. x e. S
      E. D e. ( Base ` W )
        ( Q3527250HasComplexDerivWithinAt W F S x D )
  ) $.
$}

${
  $d F W l u $.

  q3527250-diff-cont-on-cl-definition $a |- (
    ( Q3527250DiffContOnCl W F l u )
    <->
    (
      ( Q3527250DifferentiableOn
        W F ( Q3527250OpenStrip l u ) )
      /\
      ( Q3527250ContinuousOn
        W F ( Q3527250ClosureStrip l u ) )
    )
  ) $.
$}

${
  $d B F S W z $.

  q3527250-bdd-above-definition $a |- (
    ( Q3527250BddAbove W F S )
    <->
    E. B e. RR
      A. z e. S
        (
          ( ( norm ` W ) ` ( F ` z ) )
          <_
          B
        )
  ) $.
$}

${
  $d F W x y $.

  q3527250-ssup-norm-im-definition $a |- (
    Q3527250SupNormIm W F x
  ) = sup (
    ran (
      y e. { y e. CC | ( Re ` y ) = x } |->
        ( ( norm ` W ) ` ( F ` y ) )
    )
    ,
    RR
    ,
    <
  ) $.
$}

${
  $d F W l u z $.

  q3527250-interp-definition $a |- (
    Q3527250Interp W F l u z
  ) = if (
    (
      ( Q3527250SupNormIm W F l ) = 0
      \/
      ( Q3527250SupNormIm W F u ) = 0
    )
    ,
    0
    ,
    (
      (
        ( Q3527250SupNormIm W F l )
        ^c
        ( 1 - ( ( z - l ) / ( u - l ) ) )
      )
      x.
      (
        ( Q3527250SupNormIm W F u )
        ^c
        ( ( z - l ) / ( u - l ) )
      )
    )
  ) $.
$}

${
  $d F W l u z $.

  thousand-theorems-q3527250-hadamard-three-lines $a |-
    A. W e. { w e. NrmVec | ( Scalar ` w ) = CCfld }
      A. F e. ( ( Base ` W ) ^m CC )
        A. l e. RR
          A. u e. RR
            A. z e. CC
              (
                (
                  (
                    l < u
                    /\
                    z e. ( Q3527250ClosedStrip l u )
                  )
                  /\
                  (
                    ( Q3527250DiffContOnCl W F l u )
                    /\
                    (
                      Q3527250BddAbove
                      W F ( Q3527250ClosedStrip l u )
                    )
                  )
                )
                ->
                (
                  ( ( norm ` W ) ` ( F ` z ) )
                  <_
                  ( abs ` ( Q3527250Interp W F l u z ) )
                )
              )
  $.
$}
