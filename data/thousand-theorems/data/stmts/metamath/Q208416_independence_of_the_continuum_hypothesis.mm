$(
  Statement-only formalization of Thousand Theorems corpus artifact Q208416
  (thousand-theorems__metamath__Q208416), "Independence of the continuum
  hypothesis": ZFC has a model satisfying the continuum hypothesis and a
  model satisfying its negation, equivalently neither CH nor its negation is
  provable in ZFC. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's Godel-coded formulas and satisfaction operation are used with an
  arbitrary domain D and arbitrary binary membership relation R.  Q208416Valid
  says that every valuation in D satisfies a coded formula.  Q208416ZFCModel
  requires a nonempty relational model whose carrier relation is extensional,
  and which satisfies the standard pure-membership ZF axioms, every instance
  of Replacement, and the displayed closed Choice sentence.  The explicit
  Q208416Extensional condition is essential because SetMM's coded equality =g
  means equality of R-predecessors; extensionality makes it coincide with
  ambient equality on D.  Thus the ambient equalities used below for ordinal
  trichotomy, pairs, and function uniqueness have the same meaning as coded
  equality in Choice and Replacement.  Over ZF, Replacement is equivalent to
  the source's strong Collection scheme, Choice is equivalent to its Zorn
  axiom, and the source's primitive empty-set, ordered-pair, union, powerset,
  and omega symbols form a conservative definitional extension.

  Q208416CH is entirely internal to the relational model.  Its ordinals,
  least limit ordinal, powerset, ordered pairs, functions, and surjections are
  all interpreted through R.  The comparison Q208416AtMost A B says that an
  internally represented subset of B surjects onto A, matching the source
  definition.  Thus Q208416CH states that every internal ordinal A satisfies
  A <= omega or P(omega) <= A.

  By first-order completeness, the two internal model existences in the final
  unproved $a assertion are respectively equivalent to non-provability of
  not-CH and non-provability of CH in the source theory.
$)

$c
  Q208416Choice Q208416Valid Q208416Extensional Q208416ZFCModel
  Q208416Subset Q208416Transitive Q208416Trichotomous
  Q208416WellFounded Q208416Ordinal Q208416Empty
  Q208416Limit Q208416Omega Q208416Power
  Q208416Singleton Q208416UnorderedPair Q208416OrderedPair
  Q208416SurjSubset Q208416AtMost Q208416CH
$.

q208416-choice-syntax $a class Q208416Choice $.
q208416-valid-syntax $a wff ( Q208416Valid D R U ) $.
q208416-extensional-syntax $a wff ( Q208416Extensional D R ) $.
q208416-zfc-model-syntax $a wff ( Q208416ZFCModel D R ) $.
q208416-subset-syntax $a wff ( Q208416Subset D R A B ) $.
q208416-transitive-syntax $a wff ( Q208416Transitive D R A ) $.
q208416-trichotomous-syntax $a wff ( Q208416Trichotomous D R A ) $.
q208416-well-founded-syntax $a wff ( Q208416WellFounded D R A ) $.
q208416-ordinal-syntax $a wff ( Q208416Ordinal D R A ) $.
q208416-empty-syntax $a wff ( Q208416Empty D R A ) $.
q208416-limit-syntax $a wff ( Q208416Limit D R A B ) $.
q208416-omega-syntax $a wff ( Q208416Omega D R A ) $.
q208416-power-syntax $a wff ( Q208416Power D R A B ) $.
q208416-singleton-syntax $a wff ( Q208416Singleton D R A B ) $.
q208416-unordered-pair-syntax
  $a wff ( Q208416UnorderedPair D R A B C ) $.
q208416-ordered-pair-syntax
  $a wff ( Q208416OrderedPair D R A B C ) $.
q208416-surj-subset-syntax
  $a wff ( Q208416SurjSubset D R F A B ) $.
q208416-at-most-syntax $a wff ( Q208416AtMost D R A B ) $.
q208416-ch-syntax $a wff ( Q208416CH D R ) $.

q208416-valid-definition $a |- (
  ( Q208416Valid D R U )
  <->
  ( ( ( ( D Sat R ) ` _om ) ` U ) = ( D ^m _om ) )
) $.

${
  $d D R x y z $.
  q208416-extensional-definition $a |- (
    ( Q208416Extensional D R )
    <->
    A. x e. D A. y e. D
      (
        A. z e. D
          (
            <. z , x >. e. R
            <->
            <. z , y >. e. R
          )
        ->
        x = y
      )
  ) $.
$}

$(
  This is the closed pure-membership Choice sentence used in the ZFC model
  predicate.  Variable indices are: 0 family, 1 and 2 family members,
  3 selected element, and 4 choice set.
$)
q208416-choice-definition $a |- Q208416Choice =
  A.g (/) (
    (
      (
        A.g 1o (
          ( 1o e.g (/) )
          ->g
          E.g 2o ( 2o e.g 1o )
        )
        /\g
        A.g 1o A.g 2o (
          (
            (
              ( 1o e.g (/) )
              /\g
              ( 2o e.g (/) )
            )
            /\g
            -.g ( 1o =g 2o )
          )
          ->g
          -.g E.g 3o (
            ( 3o e.g 1o )
            /\g
            ( 3o e.g 2o )
          )
        )
      )
      ->g
      E.g 4o A.g 1o (
        ( 1o e.g (/) )
        ->g
        E.g 3o (
          (
            ( 3o e.g 1o )
            /\g
            ( 3o e.g 4o )
          )
          /\g
          A.g 2o (
            (
              ( 2o e.g 1o )
              /\g
              ( 2o e.g 4o )
            )
            ->g
            ( 2o =g 3o )
          )
        )
      )
    )
  ) $.

${
  $d D R u $.
  q208416-zfc-model-definition $a |- (
    ( Q208416ZFCModel D R )
    <->
    (
      (
        (
          D =/= (/)
          /\
          R C_ ( D X. D )
        )
        /\
        ( Q208416Extensional D R )
      )
      /\
      (
        (
          ( Q208416Valid D R AxPow )
          /\
          ( Q208416Valid D R AxUn )
        )
        /\
        (
          (
            ( Q208416Valid D R AxReg )
            /\
            ( Q208416Valid D R AxInf )
          )
          /\
          A. u e. ( Fmla ` _om )
            ( Q208416Valid D R ( AxRep ` u ) )
        )
        /\
        ( Q208416Valid D R Q208416Choice )
      )
    )
  ) $.
$}

${
  $d D R A B x $.
  q208416-subset-definition $a |- (
    ( Q208416Subset D R A B )
    <->
    (
      (
        A e. D
        /\
        B e. D
      )
      /\
      A. x e. D
        (
          <. x , A >. e. R
          ->
          <. x , B >. e. R
        )
    )
  ) $.
$}

${
  $d D R A x y $.
  q208416-transitive-definition $a |- (
    ( Q208416Transitive D R A )
    <->
    (
      A e. D
      /\
      A. x e. D
        (
          <. x , A >. e. R
          ->
          A. y e. D
            (
              <. y , x >. e. R
              ->
              <. y , A >. e. R
            )
        )
    )
  ) $.
$}

${
  $d D R A x y $.
  q208416-trichotomous-definition $a |- (
    ( Q208416Trichotomous D R A )
    <->
    A. x e. D A. y e. D
      (
        (
          <. x , A >. e. R
          /\
          <. y , A >. e. R
        )
        ->
        (
          x = y
          \/
          (
            <. x , y >. e. R
            \/
            <. y , x >. e. R
          )
        )
      )
  ) $.
$}

${
  $d D R A s x y $.
  q208416-well-founded-definition $a |- (
    ( Q208416WellFounded D R A )
    <->
    A. s e. D
      (
        (
          ( Q208416Subset D R s A )
          /\
          E. x e. D <. x , s >. e. R
        )
        ->
        E. x e. D
          (
            <. x , s >. e. R
            /\
            A. y e. D
              (
                <. y , s >. e. R
                ->
                -. <. y , x >. e. R
              )
          )
      )
  ) $.
$}

q208416-ordinal-definition $a |- (
  ( Q208416Ordinal D R A )
  <->
  (
    ( Q208416Transitive D R A )
    /\
    (
      ( Q208416WellFounded D R A )
      /\
      ( Q208416Trichotomous D R A )
    )
  )
) $.

${
  $d D R A x $.
  q208416-empty-definition $a |- (
    ( Q208416Empty D R A )
    <->
    (
      A e. D
      /\
      A. x e. D -. <. x , A >. e. R
    )
  ) $.
$}

${
  $d D R A B x y $.
  q208416-limit-definition $a |- (
    ( Q208416Limit D R A B )
    <->
    (
      (
        ( Q208416Empty D R A )
        /\
        <. A , B >. e. R
      )
      /\
      A. x e. D
        (
          <. x , B >. e. R
          ->
          E. y e. D
            (
              <. y , B >. e. R
              /\
              <. x , y >. e. R
            )
        )
    )
  ) $.
$}

${
  $d D R A a e $.
  q208416-omega-definition $a |- (
    ( Q208416Omega D R A )
    <->
    (
      (
        A e. D
        /\
        ( Q208416Ordinal D R A )
      )
      /\
      E. e e. D
        (
          ( Q208416Limit D R e A )
          /\
          A. a e. D
            (
              (
                ( Q208416Ordinal D R a )
                /\
                ( Q208416Limit D R e a )
              )
              ->
              ( Q208416Subset D R A a )
            )
        )
    )
  ) $.
$}

${
  $d D R A B x $.
  q208416-power-definition $a |- (
    ( Q208416Power D R A B )
    <->
    (
      (
        A e. D
        /\
        B e. D
      )
      /\
      A. x e. D
        (
          <. x , B >. e. R
          <->
          ( Q208416Subset D R x A )
        )
    )
  ) $.
$}

${
  $d D R A B x $.
  q208416-singleton-definition $a |- (
    ( Q208416Singleton D R A B )
    <->
    (
      (
        A e. D
        /\
        B e. D
      )
      /\
      A. x e. D
        (
          <. x , A >. e. R
          <->
          x = B
        )
    )
  ) $.
$}

${
  $d D R A B C x $.
  q208416-unordered-pair-definition $a |- (
    ( Q208416UnorderedPair D R A B C )
    <->
    (
      (
        A e. D
        /\
        (
          B e. D
          /\
          C e. D
        )
      )
      /\
      A. x e. D
        (
          <. x , A >. e. R
          <->
          (
            x = B
            \/
            x = C
          )
        )
    )
  ) $.
$}

${
  $d D R A B C s t $.
  q208416-ordered-pair-definition $a |- (
    ( Q208416OrderedPair D R A B C )
    <->
    E. s e. D E. t e. D
      (
        ( Q208416Singleton D R s B )
        /\
        (
          ( Q208416UnorderedPair D R t B C )
          /\
          ( Q208416UnorderedPair D R A s t )
        )
      )
  ) $.
$}

${
  $d D R F A B q r x y z $.
  q208416-surj-subset-definition $a |- (
    ( Q208416SurjSubset D R F A B )
    <->
    (
      F e. D
      /\
      (
        A. q e. D
          (
            <. q , F >. e. R
            ->
            E. x e. D E. y e. D
              (
                (
                  <. x , A >. e. R
                  /\
                  <. y , B >. e. R
                )
                /\
                ( Q208416OrderedPair D R q x y )
              )
          )
        /\
        (
          A. x e. D A. y e. D A. z e. D
            (
              (
                (
                  <. x , A >. e. R
                  /\
                  (
                    <. y , B >. e. R
                    /\
                    <. z , B >. e. R
                  )
                )
                /\
                (
                  (
                    E. q e. D
                      (
                        <. q , F >. e. R
                        /\
                        ( Q208416OrderedPair D R q x y )
                      )
                  )
                  /\
                  (
                    E. r e. D
                      (
                        <. r , F >. e. R
                        /\
                        ( Q208416OrderedPair D R r x z )
                      )
                  )
                )
              )
              ->
              y = z
            )
          /\
          A. y e. D
            (
              <. y , B >. e. R
              ->
              E. x e. D E. q e. D
                (
                  (
                    <. x , A >. e. R
                    /\
                    <. q , F >. e. R
                  )
                  /\
                  ( Q208416OrderedPair D R q x y )
                )
            )
        )
      )
    )
  ) $.
$}

${
  $d D R A B f $.
  q208416-at-most-definition $a |- (
    ( Q208416AtMost D R A B )
    <->
    E. f e. D
      ( Q208416SurjSubset D R f B A )
  ) $.
$}

${
  $d D R a p w $.
  q208416-ch-definition $a |- (
    ( Q208416CH D R )
    <->
    E. w e. D E. p e. D
      (
        (
          ( Q208416Omega D R w )
          /\
          ( Q208416Power D R w p )
        )
        /\
        A. a e. D
          (
            ( Q208416Ordinal D R a )
            ->
            (
              ( Q208416AtMost D R a w )
              \/
              ( Q208416AtMost D R p a )
            )
          )
      )
  ) $.
$}

${
  $d D E M R $.
  thousand-theorems-q208416-independence-of-the-continuum-hypothesis $a |- (
    (
      E. D E. R
        (
          ( Q208416ZFCModel D R )
          /\
          ( Q208416CH D R )
        )
    )
    /\
    (
      E. M E. E
        (
          ( Q208416ZFCModel M E )
          /\
          -. ( Q208416CH M E )
        )
    )
  ) $.
$}
