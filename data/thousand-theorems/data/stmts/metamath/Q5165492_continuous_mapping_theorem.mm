$(
  Statement-only formalization of Thousand Theorems corpus artifact Q5165492
  (thousand-theorems__metamath__Q5165492), "Continuous mapping theorem":
  composing random variables that converge in distribution along an arbitrary
  filter with a continuous map preserves convergence in distribution. This
  root artifact file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q5165492LeanFilter gives exactly the four axioms of Lean's Filter structure,
  including the possibly improper filter. This avoids the nontriviality
  condition built into SetMM's native Fil class.

  Q5165492AEMeasurable says that a function agrees outside a measurable null
  set with a measurable function. Q5165492Map uses such a measurable version
  to define its pushforward probability measure. The result is independent of
  the chosen version because two versions agree almost everywhere.

  Q5165492BoundedContinuous is the class of bounded continuous real-valued
  functions. Q5165492Integral defines their real integrals by L1 approximation
  with measurable finite-range functions and convergence of SetMM's simple
  integrals. Q5165492WeakTendsto requires convergence, along the given filter,
  of these genuine integrals. This is the bounded-continuous-test-function
  characterization of the weak topology on mathlib's ProbabilityMeasure.
  Q5165492TendstoInDistribution then expands the source structure as weak
  convergence of the pushforward laws, retaining its almost-everywhere
  measurability data. The local integral construction avoids SetMM's unfinished
  general itgm operator.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations in this root artifact are syntax or faithful
  definitions. This root artifact declares no $p statement; the included
  lib/set.mm supplies the independently verified standard-library proofs.
$)

$c Q5165492LeanFilter Q5165492AEMeasurable Q5165492Map
   Q5165492BoundedContinuous Q5165492RealTendsto
   Q5165492SeqTendsto Q5165492Simple Q5165492SimpleIntegral
   Q5165492LIntegral Q5165492Diff Q5165492L1Distance
   Q5165492HasIntegral Q5165492Integral
   Q5165492WeakTendsto Q5165492TendstoInDistribution $.

q5165492-lean-filter-syntax
  $a wff ( Q5165492LeanFilter L I ) $.
q5165492-aemeasurable-syntax
  $a wff ( Q5165492AEMeasurable M T H ) $.
q5165492-map-syntax
  $a wff ( Q5165492Map M T H P ) $.
q5165492-bounded-continuous-syntax
  $a wff ( Q5165492BoundedContinuous J H ) $.
q5165492-real-tendsto-syntax
  $a wff ( Q5165492RealTendsto L I S z ) $.
q5165492-seq-tendsto-syntax
  $a wff ( Q5165492SeqTendsto W S z ) $.
q5165492-simple-syntax
  $a wff ( Q5165492Simple M G ) $.
q5165492-simple-integral-syntax
  $a class ( Q5165492SimpleIntegral M G ) $.
q5165492-lintegral-syntax
  $a class ( Q5165492LIntegral M H ) $.
q5165492-diff-syntax
  $a class ( Q5165492Diff M H K ) $.
q5165492-l1-distance-syntax
  $a class ( Q5165492L1Distance M H K ) $.
q5165492-has-integral-syntax
  $a wff ( Q5165492HasIntegral M H y ) $.
q5165492-integral-syntax
  $a class ( Q5165492Integral M H ) $.
q5165492-weak-tendsto-syntax
  $a wff ( Q5165492WeakTendsto J L I P Q ) $.
q5165492-tendsto-in-distribution-syntax
  $a wff (
    Q5165492TendstoInDistribution J T I L M N X Z
  ) $.

${
  $d A B I L $.

  q5165492-lean-filter-definition $a |- (
    ( Q5165492LeanFilter L I )
    <->
    (
      L C_ ~P I
      /\
      (
        I e. L
        /\
        (
          A. A e. L A. B e. ~P I
            ( A C_ B -> B e. L )
          /\
          A. A e. L A. B e. L
            ( A i^i B ) e. L
        )
      )
    )
  ) $.
$}

${
  $d H K M N T x $.

  q5165492-aemeasurable-definition $a |- (
    ( Q5165492AEMeasurable M T H )
    <->
    (
      H : U. dom M --> U. T
      /\
      E. K e. ( dom M MblFnM T )
        E. N e. dom M
          (
            ( M ` N ) = 0
            /\
            A. x e. ( U. dom M \ N )
              ( H ` x ) = ( K ` x )
          )
    )
  ) $.
$}

${
  $d B H K M N P T x $.

  q5165492-map-definition $a |- (
    ( Q5165492Map M T H P )
    <->
    (
      (
        H : U. dom M --> U. T
        /\
        (
          P e. Prob
          /\
          dom P = T
        )
      )
      /\
      E. K e. ( dom M MblFnM T )
        E. N e. dom M
          (
            (
              ( M ` N ) = 0
              /\
              A. x e. ( U. dom M \ N )
                ( H ` x ) = ( K ` x )
            )
            /\
            A. B e. T
              ( P ` B ) = ( M ` ( `' K " B ) )
          )
    )
  ) $.
$}

${
  $d H J c x $.

  q5165492-bounded-continuous-definition $a |- (
    ( Q5165492BoundedContinuous J H )
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
  $d I L S V i z $.

  q5165492-real-tendsto-definition $a |- (
    ( Q5165492RealTendsto L I S z )
    <->
    (
      (
        S : I --> RR
        /\
        z e. RR
      )
      /\
      A. V e. ( TopOpen ` RRfld )
        (
          z e. V
          ->
          { i e. I | ( S ` i ) e. V } e. L
        )
    )
  ) $.
$}

${
  $d S W z $.

  q5165492-seq-tendsto-definition $a |- (
    ( Q5165492SeqTendsto W S z )
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

  q5165492-simple-definition $a |- (
    ( Q5165492Simple M G )
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

  q5165492-simple-integral-definition $a |- (
    Q5165492SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q5165492-lintegral-definition $a |- (
    Q5165492LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q5165492Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q5165492SimpleIntegral M G )
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

  q5165492-diff-definition $a |- (
    Q5165492Diff M H K
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

  q5165492-l1-distance-definition $a |- (
    Q5165492L1Distance M H K
  ) =
    (
      Q5165492LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` RRfld )
          `
          ( ( Q5165492Diff M H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M n s y $.

  q5165492-has-integral-definition $a |- (
    ( Q5165492HasIntegral M H y )
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
            Q5165492SeqTendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q5165492L1Distance M H ( s ` n ) ) )
            0
            /\
            Q5165492SeqTendsto
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

  q5165492-integral-definition $a |- (
    Q5165492Integral M H
    =
    (
      iota_ y e. RR
        ( Q5165492HasIntegral M H y )
    )
  ) $.
$}

${
  $d H I J L P Q i $.

  q5165492-weak-tendsto-definition $a |- (
    ( Q5165492WeakTendsto J L I P Q )
    <->
    (
      (
        P : I --> Prob
        /\
        Q e. Prob
      )
      /\
      A. H
        (
          ( Q5165492BoundedContinuous J H )
          ->
          (
            Q5165492RealTendsto
            L
            I
            (
              i e. I |->
              ( Q5165492Integral ( P ` i ) H )
            )
            ( Q5165492Integral Q H )
          )
        )
    )
  ) $.
$}

${
  $d I J L M N P Q T X Z i $.

  q5165492-tendsto-in-distribution-definition $a |- (
    (
      Q5165492TendstoInDistribution J T I L M N X Z
    )
    <->
    (
      ( Q5165492LeanFilter L I )
      /\
      (
        (
          A. i e. I
            ( Q5165492AEMeasurable ( M ` i ) T ( X ` i ) )
          /\
          ( Q5165492AEMeasurable N T Z )
        )
        /\
        E. P E. Q
          (
            (
              (
                P : I --> Prob
                /\
                Q e. Prob
              )
              /\
              (
                A. i e. I
                  (
                    Q5165492Map
                    ( M ` i )
                    T
                    ( X ` i )
                    ( P ` i )
                  )
                /\
                ( Q5165492Map N T Z Q )
              )
            )
            /\
            ( Q5165492WeakTendsto J L I P Q )
          )
      )
    )
  ) $.
$}

${
  $d E F G I J K L M N R S T U X Z i $.

  thousand-theorems-q5165492-continuous-mapping-theorem $a |-
    A. I A. S A. M A. R A. N
      A. E A. J A. T
        A. F A. K A. U
          A. X A. L A. Z A. G
            (
              (
                (
                  S : I --> U. ran sigAlgebra
                  /\
                  (
                    M : I --> Prob
                    /\
                    A. i e. I
                      dom ( M ` i ) = ( S ` i )
                  )
                )
                /\
                (
                  (
                    R e. U. ran sigAlgebra
                    /\
                    (
                      N e. Prob
                      /\
                      dom N = R
                    )
                  )
                  /\
                  (
                    (
                      T e. U. ran sigAlgebra
                      /\
                      (
                        U. T = E
                        /\
                        (
                          J e. ( TopOn ` E )
                          /\
                          J C_ T
                        )
                      )
                    )
                    /\
                    (
                      U e. U. ran sigAlgebra
                      /\
                      (
                        U. U = F
                        /\
                        (
                          K e. ( TopOn ` F )
                          /\
                          U = ( sigaGen ` K )
                        )
                      )
                    )
                  )
                )
              )
              ->
              (
                (
                  (
                    X Fn I
                    /\
                    A. i e. I
                      ( X ` i ) : U. ( S ` i ) --> E
                  )
                  /\
                  (
                    Z : U. R --> E
                    /\
                    G : E --> F
                  )
                )
                ->
                (
                  (
                    G e. ( J Cn K )
                    /\
                    (
                      Q5165492TendstoInDistribution
                      J T I L M N X Z
                    )
                  )
                  ->
                  (
                    Q5165492TendstoInDistribution
                    K
                    U
                    I
                    L
                    M
                    N
                    ( i e. I |-> ( G o. ( X ` i ) ) )
                    ( G o. Z )
                  )
                )
              )
            )
  $.
$}
