$(
  Statement-only formalization of Thousand Theorems corpus artifact Q643826
  (thousand-theorems__metamath__Q643826), "Slutsky's theorem": if one family
  converges in distribution and another converges in measure to a constant,
  then applying an arbitrary continuous function to their paired values
  preserves convergence in distribution. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Q643826SeminormedAddCommGroup is an arbitrary Abelian group equipped with a
  real-valued seminorm; importantly, no definiteness axiom is imposed.
  Q643826NormTopology is its seminorm topology. Thus these definitions retain
  Lean's full SeminormedAddCommGroup generality rather than narrowing to
  normed vector spaces.

  Q643826LeanFilter gives exactly the four axioms of Lean's Filter structure,
  including the possibly improper filter. Q643826CountablyGenerated gives it
  a countable refinement basis.

  Q643826AEMeasurable says that a function agrees outside a measurable null
  set with a measurable function. Q643826Map uses such a version to define
  the pushforward law. Q643826Integral defines real expectations as limits of
  SetMM simple integrals along L1-approximating measurable finite-range
  functions. Q643826WeakTendsto uses these expectations of bounded continuous
  real-valued test functions, and Q643826TendstoInDistribution expands
  convergence in distribution as weak convergence of pushforward probability
  measures.

  Q643826TendstoInMeasure uses the norm formulation equivalent to mathlib's
  definition: for every positive real epsilon, the outer measures of the sets
  where the norm-distance from the constant is at least epsilon converge to
  zero in the extended-nonnegative-real topology.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions. This root
  artifact declares no $p statement; the included lib/set.mm supplies the
  independently verified standard-library proofs.
$)

$c Q643826SeminormedAddCommGroup Q643826NormTopology
   Q643826LeanFilter Q643826CountablyGenerated
   Q643826AEMeasurable Q643826Map Q643826BoundedContinuous
   Q643826Tendsto Q643826SeqTendsto
   Q643826Simple Q643826SimpleIntegral Q643826LIntegral
   Q643826Diff Q643826L1Distance Q643826HasIntegral Q643826Integral
   Q643826WeakTendsto
   Q643826TendstoInDistribution Q643826TendstoInMeasure $.

q643826-seminormed-add-comm-group-syntax
  $a wff ( Q643826SeminormedAddCommGroup V ) $.
q643826-norm-topology-syntax
  $a class ( Q643826NormTopology V ) $.
q643826-lean-filter-syntax
  $a wff ( Q643826LeanFilter L I ) $.
q643826-countably-generated-syntax
  $a wff ( Q643826CountablyGenerated L I ) $.
q643826-aemeasurable-syntax
  $a wff ( Q643826AEMeasurable M T H ) $.
q643826-map-syntax
  $a wff ( Q643826Map M T H P ) $.
q643826-bounded-continuous-syntax
  $a wff ( Q643826BoundedContinuous J H ) $.
q643826-tendsto-syntax
  $a wff ( Q643826Tendsto J L I S z ) $.
q643826-seq-tendsto-syntax
  $a wff ( Q643826SeqTendsto W S z ) $.
q643826-simple-syntax
  $a wff ( Q643826Simple M G ) $.
q643826-simple-integral-syntax
  $a class ( Q643826SimpleIntegral M G ) $.
q643826-lintegral-syntax
  $a class ( Q643826LIntegral M H ) $.
q643826-diff-syntax
  $a class ( Q643826Diff M H K ) $.
q643826-l1-distance-syntax
  $a class ( Q643826L1Distance M H K ) $.
q643826-has-integral-syntax
  $a wff ( Q643826HasIntegral M H y ) $.
q643826-integral-syntax
  $a class ( Q643826Integral M H ) $.
q643826-weak-tendsto-syntax
  $a wff ( Q643826WeakTendsto J L I P Q ) $.
q643826-tendsto-in-distribution-syntax
  $a wff (
    Q643826TendstoInDistribution J T I L M N X Z
  ) $.
q643826-tendsto-in-measure-syntax
  $a wff ( Q643826TendstoInMeasure V M I L Y c ) $.

${
  $d V x y $.

  q643826-seminormed-add-comm-group-definition $a |- (
    ( Q643826SeminormedAddCommGroup V )
    <->
    (
      V e. Abel
      /\
      (
        ( norm ` V ) : ( Base ` V ) --> RR
        /\
        (
          ( ( norm ` V ) ` ( 0g ` V ) ) = 0
          /\
          (
            A. x e. ( Base ` V )
              0 <_ ( ( norm ` V ) ` x )
            /\
            (
              A. x e. ( Base ` V )
                (
                  ( norm ` V )
                  `
                  ( ( -g ` V ) ` x )
                )
                =
                ( ( norm ` V ) ` x )
              /\
              A. x e. ( Base ` V )
                A. y e. ( Base ` V )
                  (
                    ( norm ` V )
                    `
                    ( x ( +g ` V ) y )
                  )
                  <_
                  (
                    ( ( norm ` V ) ` x )
                    +
                    ( ( norm ` V ) ` y )
                  )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d O V r x y $.

  q643826-norm-topology-definition $a |- (
    Q643826NormTopology V
  ) = {
    O e. ~P ( Base ` V )
    |
    A. x e. O
      E. r e. RR+
        A. y e. ( Base ` V )
          (
            (
              ( norm ` V )
              `
              (
                x
                ( +g ` V )
                ( ( -g ` V ) ` y )
              )
            )
            <
            r
            ->
            y e. O
          )
  } $.
$}

${
  $d A B I L $.

  q643826-lean-filter-definition $a |- (
    ( Q643826LeanFilter L I )
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
  $d A B I L n $.

  q643826-countably-generated-definition $a |- (
    ( Q643826CountablyGenerated L I )
    <->
    E. B
      (
        B : NN0 --> L
        /\
        A. A e. L E. n e. NN0
          ( B ` n ) C_ A
      )
  ) $.
$}

${
  $d H K M N T x $.

  q643826-aemeasurable-definition $a |- (
    ( Q643826AEMeasurable M T H )
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

  q643826-map-definition $a |- (
    ( Q643826Map M T H P )
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

  q643826-bounded-continuous-definition $a |- (
    ( Q643826BoundedContinuous J H )
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
  $d I J L O S i z $.

  q643826-tendsto-definition $a |- (
    ( Q643826Tendsto J L I S z )
    <->
    (
      (
        S : I --> U. J
        /\
        z e. U. J
      )
      /\
      A. O e. J
        (
          z e. O
          ->
          { i e. I | ( S ` i ) e. O } e. L
        )
    )
  ) $.
$}

${
  $d S W z $.

  q643826-seq-tendsto-definition $a |- (
    ( Q643826SeqTendsto W S z )
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

  q643826-simple-definition $a |- (
    ( Q643826Simple M G )
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

  q643826-simple-integral-definition $a |- (
    Q643826SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q643826-lintegral-definition $a |- (
    Q643826LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q643826Simple M G )
            /\
            (
              A. x e. U. dom M
                ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q643826SimpleIntegral M G )
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

  q643826-diff-definition $a |- (
    Q643826Diff M H K
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

  q643826-l1-distance-definition $a |- (
    Q643826L1Distance M H K
  ) =
    (
      Q643826LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` RRfld )
          `
          ( ( Q643826Diff M H K ) ` x )
        )
      )
    )
  ) $.
$}

${
  $d H M n s y $.

  q643826-has-integral-definition $a |- (
    ( Q643826HasIntegral M H y )
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
            Q643826SeqTendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q643826L1Distance M H ( s ` n ) ) )
            0
            /\
            Q643826SeqTendsto
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

  q643826-integral-definition $a |- (
    Q643826Integral M H
    =
    (
      iota_ y e. RR
        ( Q643826HasIntegral M H y )
    )
  ) $.
$}

${
  $d H I J L P Q i $.

  q643826-weak-tendsto-definition $a |- (
    ( Q643826WeakTendsto J L I P Q )
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
          ( Q643826BoundedContinuous J H )
          ->
          (
            Q643826Tendsto
            ( TopOpen ` RRfld )
            L
            I
            (
              i e. I |->
              ( Q643826Integral ( P ` i ) H )
            )
            ( Q643826Integral Q H )
          )
        )
    )
  ) $.
$}

${
  $d I J L M N P Q T X Z i $.

  q643826-tendsto-in-distribution-definition $a |- (
    (
      Q643826TendstoInDistribution J T I L M N X Z
    )
    <->
    (
      ( Q643826LeanFilter L I )
      /\
      (
        (
          A. i e. I
            ( Q643826AEMeasurable ( M ` i ) T ( X ` i ) )
          /\
          ( Q643826AEMeasurable N T Z )
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
                    Q643826Map
                    ( M ` i )
                    T
                    ( X ` i )
                    ( P ` i )
                  )
                /\
                ( Q643826Map N T Z Q )
              )
            )
            /\
            ( Q643826WeakTendsto J L I P Q )
          )
      )
    )
  ) $.
$}

${
  $d I L M V Y c i r x $.

  q643826-tendsto-in-measure-definition $a |- (
    ( Q643826TendstoInMeasure V M I L Y c )
    <->
    (
      (
        Y Fn I
        /\
        (
          A. i e. I
            ( Y ` i ) : U. dom M --> ( Base ` V )
          /\
          c e. ( Base ` V )
        )
      )
      /\
      A. r e. RR+
        (
          Q643826Tendsto
          ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
          L
          I
          (
            i e. I |->
            (
              ( toOMeas ` M )
              `
              {
                x e. U. dom M
                |
                r
                <_
                (
                  ( norm ` V )
                  `
                  (
                    ( ( Y ` i ) ` x )
                    ( +g ` V )
                    ( ( -g ` V ) ` c )
                  )
                )
              }
            )
          )
          0
        )
    )
  ) $.
$}

${
  $d C G I K L M N R S U V W X Y Z c i x $.

  thousand-theorems-q643826-slutsky-s-theorem $a |-
    A. I A. L
      A. S A. M A. R A. N
        A. V A. W
          A. C A. K A. U
            A. X A. Y A. Z A. c A. G
              (
                (
                  (
                    S e. U. ran sigAlgebra
                    /\
                    (
                      M e. Prob
                      /\
                      dom M = S
                    )
                  )
                  /\
                  (
                    R e. U. ran sigAlgebra
                    /\
                    (
                      N e. Prob
                      /\
                      dom N = R
                    )
                  )
                )
                /\
                (
                  (
                    ( Q643826SeminormedAddCommGroup V )
                    /\
                    (
                      ( Q643826NormTopology V ) e. 2ndc
                      /\
                      (
                        Q643826SeminormedAddCommGroup W
                      )
                    )
                  )
                  /\
                  (
                    ( Q643826NormTopology W ) e. 2ndc
                    /\
                    (
                      K e. ( TopOn ` C )
                      /\
                      (
                        U e. U. ran sigAlgebra
                        /\
                        (
                          U. U = C
                          /\
                          U = ( sigaGen ` K )
                        )
                      )
                    )
                  )
                )
                ->
                (
                  (
                    (
                      ( Q643826LeanFilter L I )
                      /\
                      ( Q643826CountablyGenerated L I )
                    )
                    /\
                    (
                      (
                        X Fn I
                        /\
                        A. i e. I
                          ( X ` i ) :
                          U. S --> ( Base ` V )
                      )
                      /\
                      (
                        Y Fn I
                        /\
                        A. i e. I
                          ( Y ` i ) :
                          U. S --> ( Base ` W )
                      )
                    )
                  )
                  /\
                  (
                    (
                      Z : U. R --> ( Base ` V )
                      /\
                      c e. ( Base ` W )
                    )
                    /\
                    G :
                    (
                      ( Base ` V )
                      X.
                      ( Base ` W )
                    )
                    --> C
                  )
                  ->
                  (
                    (
                      G e.
                        (
                          (
                            ( Q643826NormTopology V )
                            tX
                            ( Q643826NormTopology W )
                          )
                          Cn
                          K
                        )
                      /\
                      (
                        Q643826TendstoInDistribution
                        ( Q643826NormTopology V )
                        (
                          sigaGen `
                          ( Q643826NormTopology V )
                        )
                        I
                        L
                        ( i e. I |-> M )
                        N
                        X
                        Z
                      )
                    )
                    /\
                    (
                      (
                        Q643826TendstoInMeasure
                        W M I L Y c
                      )
                      /\
                      A. i e. I
                        (
                          Q643826AEMeasurable
                          M
                          (
                            sigaGen `
                            ( Q643826NormTopology W )
                          )
                          ( Y ` i )
                        )
                    )
                    ->
                    (
                      Q643826TendstoInDistribution
                      K
                      U
                      I
                      L
                      ( i e. I |-> M )
                      N
                      (
                        i e. I |->
                        (
                          x e. U. S |->
                          (
                            G
                            `
                            <.
                              ( ( X ` i ) ` x ) ,
                              ( ( Y ` i ) ` x )
                            >.
                          )
                        )
                      )
                      (
                        x e. U. R |->
                        (
                          G
                          `
                          <. ( Z ` x ) , c >.
                        )
                      )
                    )
                  )
                )
              )
  $.
$}
