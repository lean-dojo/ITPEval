$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1966978
  (thousand-theorems__metamath__Q1966978), "L&eacute;vy continuity theorem": for
  probability measures on an arbitrary finite-dimensional real inner-product
  space, weak convergence of a sequence is equivalent to pointwise convergence
  of its characteristic functions. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  V ranges over SetMM real pre-Hilbert spaces with finite dimension, exactly
  the finite-dimensional real inner-product spaces of the Lean statement.
  Q1966978ProbabilityData says that P is an NN0-indexed sequence and Q is a
  limit probability measure, all on the Borel sigma-algebra of V's norm
  topology.

  Q1966978BoundedContinuous is the class of bounded continuous real-valued
  functions on V. Q1966978WeakTendsto requires sequential convergence of their
  real integrals, the bounded-continuous-test-function characterization of the
  weak topology on probability measures.

  Q1966978Integral defines real- or complex-valued integrals as limits of
  SetMM simple integrals along L1-approximating measurable finite-range
  functions. This construction is valid for the complete codomains RRfld and
  CCfld used below and does not depend on SetMM's unfinished itgm operator.

  Q1966978Char is the complex integral of

    x |-> exp(i * inner(x,t))

  with respect to a probability measure. Q1966978CharTendsto states pointwise
  sequential convergence of these values in the complex topology. SetMM's
  inner product is linear in its first slot, and on a real inner-product space
  it is symmetric, so the displayed order agrees with Mathlib's charFun.

  Every declaration before the final one is syntax or an explicit
  bidirectional definition. The final $a declaration is the single unproved
  corpus statement, and this database contains no $p proof statement.
$)

$c Q1966978ProbabilityData Q1966978BoundedContinuous
   Q1966978SeqTendsto Q1966978Simple Q1966978SimpleIntegral
   Q1966978LIntegral Q1966978Diff Q1966978L1Distance
   Q1966978HasIntegral Q1966978Integral
   Q1966978WeakTendsto Q1966978Char Q1966978CharTendsto $.

q1966978-probability-data-syntax
  $a wff ( Q1966978ProbabilityData V P Q ) $.
q1966978-bounded-continuous-syntax
  $a wff ( Q1966978BoundedContinuous V H ) $.
q1966978-seq-tendsto-syntax
  $a wff ( Q1966978SeqTendsto W S z ) $.
q1966978-simple-syntax
  $a wff ( Q1966978Simple M G ) $.
q1966978-simple-integral-syntax
  $a class ( Q1966978SimpleIntegral M G ) $.
q1966978-lintegral-syntax
  $a class ( Q1966978LIntegral M H ) $.
q1966978-diff-syntax
  $a class ( Q1966978Diff M W H K ) $.
q1966978-l1-distance-syntax
  $a class ( Q1966978L1Distance M W H K ) $.
q1966978-has-integral-syntax
  $a wff ( Q1966978HasIntegral M W H y ) $.
q1966978-integral-syntax
  $a class ( Q1966978Integral W M H ) $.
q1966978-weak-tendsto-syntax
  $a wff ( Q1966978WeakTendsto V P Q ) $.
q1966978-char-syntax
  $a class ( Q1966978Char V M t ) $.
q1966978-char-tendsto-syntax
  $a wff ( Q1966978CharTendsto V P Q ) $.

${
  $d P Q V n $.

  q1966978-probability-data-definition $a |- (
    ( Q1966978ProbabilityData V P Q )
    <->
    (
      (
        P : NN0 --> Prob
        /\
        A. n e. NN0
          dom ( P ` n )
          =
          ( sigaGen ` ( TopOpen ` V ) )
      )
      /\
      (
        Q e. Prob
        /\
        dom Q = ( sigaGen ` ( TopOpen ` V ) )
      )
    )
  ) $.
$}

${
  $d H V c x $.

  q1966978-bounded-continuous-definition $a |- (
    ( Q1966978BoundedContinuous V H )
    <->
    (
      H e.
        (
          ( TopOpen ` V )
          Cn
          ( TopOpen ` RRfld )
        )
      /\
      E. c e. RR+
        A. x e. ( Base ` V )
          ( abs ` ( H ` x ) ) < c
    )
  ) $.
$}

${
  $d S W z $.

  q1966978-seq-tendsto-definition $a |- (
    ( Q1966978SeqTendsto W S z )
    <->
    (
      S : NN0 --> ( Base ` W )
      /\
      S ( ~~>t ` ( TopOpen ` W ) ) z
    )
  ) $.
$}

${
  $d G M $.

  q1966978-simple-definition $a |- (
    ( Q1966978Simple M G )
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

  q1966978-simple-integral-definition $a |- (
    Q1966978SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q1966978-lintegral-definition $a |- (
    Q1966978LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q1966978Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q1966978SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d H K M W x $.

  q1966978-diff-definition $a |- (
    Q1966978Diff M W H K
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

  q1966978-l1-distance-definition $a |- (
    Q1966978L1Distance M W H K
  ) =
    (
      Q1966978LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q1966978Diff M W H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M W n s y $.

  q1966978-has-integral-definition $a |- (
    ( Q1966978HasIntegral M W H y )
    <->
    (
      y e. ( Base ` W )
      /\
      E. s e. ( ( ( Base ` W ) ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            ( ( s ` n ) e. dom ( W sitg M ) )
          /\
          (
            Q1966978SeqTendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q1966978L1Distance M W H ( s ` n ) ) )
            0
            /\
            Q1966978SeqTendsto
            W
            ( n e. NN0 |-> ( ( W sitg M ) ` ( s ` n ) ) )
            y
          )
        )
    )
  ) $.
$}

${
  $d H M W y $.

  q1966978-integral-definition $a |- (
    Q1966978Integral W M H
    =
    (
      iota_ y e. ( Base ` W )
        ( Q1966978HasIntegral M W H y )
    )
  ) $.
$}

${
  $d H P Q V n $.

  q1966978-weak-tendsto-definition $a |- (
    ( Q1966978WeakTendsto V P Q )
    <->
    A. H
      (
        ( Q1966978BoundedContinuous V H )
        ->
        (
          n e. NN0 |->
          ( Q1966978Integral RRfld ( P ` n ) H )
        )
        (
          ~~>t ` ( TopOpen ` RRfld )
        )
        ( Q1966978Integral RRfld Q H )
      )
  ) $.
$}

${
  $d M V t x $.

  q1966978-char-definition $a |- (
    ( Q1966978Char V M t )
    =
    (
      Q1966978Integral
      CCfld
      M
      (
        x e. ( Base ` V ) |->
        (
          exp
          `
          (
            _i
            x.
            ( x ( .i ` V ) t )
          )
        )
      )
    )
  ) $.
$}

${
  $d P Q V n t $.

  q1966978-char-tendsto-definition $a |- (
    ( Q1966978CharTendsto V P Q )
    <->
    A. t e. ( Base ` V )
      (
        n e. NN0 |->
        ( Q1966978Char V ( P ` n ) t )
      )
      (
        ~~>t ` ( TopOpen ` CCfld )
      )
      ( Q1966978Char V Q t )
  ) $.
$}

${
  $d H M P Q V c n t x $.

  thousand-theorems-q1966978-levy-continuity-theorem $a |-
    A. V e.
      {
        v e. CPreHil |
        (
          ( Scalar ` v ) = RRfld
          /\
          ( dim ` v ) e. NN0
        )
      }
      A. P A. Q
        (
          ( Q1966978ProbabilityData V P Q )
          ->
          (
            ( Q1966978WeakTendsto V P Q )
            <->
            ( Q1966978CharTendsto V P Q )
          )
        )
  $.
$}
