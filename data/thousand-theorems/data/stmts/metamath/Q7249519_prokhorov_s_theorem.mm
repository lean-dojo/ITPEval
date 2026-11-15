$(
  Statement-only formalization of Thousand Theorems corpus artifact Q7249519
  (thousand-theorems__metamath__Q7249519), "Prokhorov's theorem": on an
  arbitrary Hausdorff Borel topological space, finite measures of uniformly
  bounded mass whose mass outside each compact set K(n) is bounded by a
  nonnegative sequence tending to zero form a compact set, provided the space
  is normal or K is monotone. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q7249519FiniteMeasures S is the class of all finite measures on the
  sigma-algebra S. Q7249519BoundedContinuous J H says that H is a bounded
  continuous real-valued function on the carrier of J.

  Q7249519Integral defines integration of such a function against a finite
  measure as the unique limit of SetMM simple integrals along an L1-
  approximating sequence of measurable finite-range functions.
  Q7249519WeakSubbase J S consists of the inverse images of real-open sets
  under integration against bounded continuous real functions. Closing this
  subbase under finite intersections and arbitrary unions gives
  Q7249519WeakTopology J S, the bounded-continuous-test-function weak topology
  on finite measures. This is the topology induced on Mathlib's FiniteMeasure
  by its weak dual representation.

  Q7249519TendstoZero and Q7249519Monotone expand the two sequence conditions.
  Q7249519Admissible is exactly the set of finite measures with total mass at
  most C and mass on the carrier-relative complement of K(n) at most u(n) for
  every natural n.

  In the final assertion J is an arbitrary Hausdorff topology on X. Its Borel
  measurable space is sigaGen(J), matching the Lean BorelSpace assumption.
  Compactness is expressed by membership of the restricted weak topology in
  Comp. Every declaration before the final one is syntax or a faithful
  definition. The final $a is the single unproved corpus statement, and this
  root file has no $p declaration.
$)

$c Q7249519FiniteMeasures Q7249519BoundedContinuous
   Q7249519SeqTendsto Q7249519Simple Q7249519SimpleIntegral
   Q7249519LIntegral Q7249519Diff Q7249519L1Distance
   Q7249519HasIntegral Q7249519Integral
   Q7249519WeakSubbase Q7249519WeakTopology Q7249519TendstoZero
   Q7249519Monotone Q7249519Admissible $.

q7249519-finite-measures-syntax
  $a class ( Q7249519FiniteMeasures S ) $.
q7249519-bounded-continuous-syntax
  $a wff ( Q7249519BoundedContinuous J H ) $.
q7249519-seq-tendsto-syntax
  $a wff ( Q7249519SeqTendsto W S z ) $.
q7249519-simple-syntax
  $a wff ( Q7249519Simple M G ) $.
q7249519-simple-integral-syntax
  $a class ( Q7249519SimpleIntegral M G ) $.
q7249519-lintegral-syntax
  $a class ( Q7249519LIntegral M H ) $.
q7249519-diff-syntax
  $a class ( Q7249519Diff M H K ) $.
q7249519-l1-distance-syntax
  $a class ( Q7249519L1Distance M H K ) $.
q7249519-has-integral-syntax
  $a wff ( Q7249519HasIntegral M H y ) $.
q7249519-integral-syntax
  $a class ( Q7249519Integral M H ) $.
q7249519-weak-subbase-syntax
  $a class ( Q7249519WeakSubbase J S ) $.
q7249519-weak-topology-syntax
  $a class ( Q7249519WeakTopology J S ) $.
q7249519-tendsto-zero-syntax
  $a wff ( Q7249519TendstoZero u ) $.
q7249519-monotone-syntax
  $a wff ( Q7249519Monotone K ) $.
q7249519-admissible-syntax
  $a class ( Q7249519Admissible J K u C ) $.

${
  $d M S $.

  q7249519-finite-measures-definition $a |- (
    Q7249519FiniteMeasures S
  ) = {
    M e. ( measures ` S ) |
    ( M ` U. S ) < +oo
  } $.
$}

${
  $d H J c x $.

  q7249519-bounded-continuous-definition $a |- (
    ( Q7249519BoundedContinuous J H )
    <->
    (
      H e. ( J Cn ( TopOpen ` RRfld ) )
      /\
      E. c e. RR+
        A. x e. U. J
          ( abs ` ( H ` x ) ) < c
    )
  ) $.
$}

${
  $d S W z $.

  q7249519-seq-tendsto-definition $a |- (
    ( Q7249519SeqTendsto W S z )
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

  q7249519-simple-definition $a |- (
    ( Q7249519Simple M G )
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

  q7249519-simple-integral-definition $a |- (
    Q7249519SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q7249519-lintegral-definition $a |- (
    Q7249519LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q7249519Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q7249519SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  ) $.
$}

${
  $d H K M x $.

  q7249519-diff-definition $a |- (
    Q7249519Diff M H K
  ) =
    ( x e. U. dom M |->
      (
        ( H ` x )
        ( +g ` RRfld )
        ( ( -g ` RRfld ) ` ( K ` x ) )
      )
    )
  $.
$}

${
  $d H K M x $.

  q7249519-l1-distance-definition $a |- (
    Q7249519L1Distance M H K
  ) =
    (
      Q7249519LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` RRfld )
          `
          ( ( Q7249519Diff M H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M n s y $.

  q7249519-has-integral-definition $a |- (
    ( Q7249519HasIntegral M H y )
    <->
    (
      y e. RR
      /\
      E. s e. ( ( RR ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            ( ( s ` n ) e. dom ( RRfld sitg M ) )
          /\
          (
            Q7249519SeqTendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q7249519L1Distance M H ( s ` n ) ) )
            0
            /\
            Q7249519SeqTendsto
            RRfld
            ( n e. NN0 |-> ( ( RRfld sitg M ) ` ( s ` n ) ) )
            y
          )
        )
    )
  ) $.
$}

${
  $d H M y $.

  q7249519-integral-definition $a |- (
    Q7249519Integral M H
    =
    (
      iota_ y e. RR
        ( Q7249519HasIntegral M H y )
    )
  ) $.
$}

${
  $d A H J M O S $.

  q7249519-weak-subbase-definition $a |- (
    Q7249519WeakSubbase J S
  ) = {
    A e. ~P ( Q7249519FiniteMeasures S ) |
    E. H E. O
      (
        ( Q7249519BoundedContinuous J H )
        /\
        O e. ( TopOpen ` RRfld )
        /\
        A = {
          M e. ( Q7249519FiniteMeasures S ) |
          ( Q7249519Integral M H ) e. O
        }
      )
  } $.
$}

${
  $d J S $.

  q7249519-weak-topology-definition $a |- (
    Q7249519WeakTopology J S
  ) = (
    topGen
    `
    (
      fi
      `
      (
        { ( Q7249519FiniteMeasures S ) }
        u.
        ( Q7249519WeakSubbase J S )
      )
    )
  ) $.
$}

${
  $d N n r u $.

  q7249519-tendsto-zero-definition $a |- (
    ( Q7249519TendstoZero u )
    <->
    (
      u : NN0 --> ( 0 [,) +oo )
      /\
      A. r e. RR+
        E. N e. NN0
          A. n e. NN0
            (
              N <_ n
              ->
              ( u ` n ) < r
            )
    )
  ) $.
$}

${
  $d K m n $.

  q7249519-monotone-definition $a |- (
    ( Q7249519Monotone K )
    <->
    A. m e. NN0
      A. n e. NN0
        (
          m <_ n
          ->
          ( K ` m ) C_ ( K ` n )
        )
  ) $.
$}

${
  $d C J K M n u $.

  q7249519-admissible-definition $a |- (
    Q7249519Admissible J K u C
  ) = {
    M e.
      (
        Q7249519FiniteMeasures
        ( sigaGen ` J )
      ) |
    (
      ( M ` U. J ) <_ C
      /\
      A. n e. NN0
        (
          M
          `
          (
            U. J
            \
            ( K ` n )
          )
        )
        <_
        ( u ` n )
    )
  } $.
$}

${
  $d C H J K M N O S X c m n r u x $.

  thousand-theorems-q7249519-prokhorov-s-theorem $a |-
    A. X A. J A. C A. u A. K
      (
        (
          J e. ( TopOn ` X )
          /\
          J e. Haus
          /\
          C e. ( 0 [,) +oo )
          /\
          u : NN0 --> ( 0 [,) +oo )
          /\
          K : NN0 --> ~P X
        )
        ->
        (
          (
            ( Q7249519TendstoZero u )
            /\
            A. n e. NN0
              ( J |`t ( K ` n ) ) e. Comp
            /\
            (
              J e. Nrm
              \/
              ( Q7249519Monotone K )
            )
          )
          ->
          (
            (
              Q7249519WeakTopology
              J
              ( sigaGen ` J )
            )
            |`t
            ( Q7249519Admissible J K u C )
          ) e. Comp
        )
      )
  $.
$}
