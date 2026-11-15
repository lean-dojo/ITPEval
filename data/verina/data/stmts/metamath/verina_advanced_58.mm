$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_58 (verina__metamath__verina_advanced_58), catalog title
  nthUglyNumber: the exact three-counter sequence-generation program returns
  the requested positive-indexed ugly number, characterized by divisibility
  only by two, three, and five and by the count of earlier ugly numbers. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA58GetD is Lean List.get! on a natural-number list, including its zero
  default outside the list. VERINA58NatSub restores Lean's truncated Nat.sub.
  VERINA58Snoc is exact append of a singleton to a word.

  VERINA58NextUgly is the source nextUgly helper. It reads the entries at the
  three counters, multiplies them by two, three, and five, chooses their
  minimum, and increments every counter whose candidate equals that minimum.
  VERINA58LoopGraph records the complete deterministic state trace of the
  recursive loop for arbitrary helper arguments. VERINA58NthUglyNumber runs
  that loop for n - 1 steps from the singleton word [1] and counters zero,
  then performs the source zero-default lookup at index n - 1. Thus the
  executable result is fixed independently of the postcondition.

  VERINA58DivideOutGraph exactly represents divideOut. For positive n and
  p greater than one, its unique residual removes the maximal power of p;
  otherwise it returns n unchanged. VERINA58IsUgly applies this helper for
  two, three, and five and returns true exactly when the final residual is
  one, with { 0 , 1 } representing Bool. VERINA58UglyCount is the length of
  the source filter of List.range, expressed as the cardinality of precisely
  those indices below the result where VERINA58IsUgly is true.

  VERINA58Pre, VERINA58Post, and the final assertion retain the source
  precondition, postcondition, and correctness proposition. The proof-valued
  precondition arguments are computationally and propositionally unused and
  are represented by the explicit antecedent. Every earlier $a is syntax or
  a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA58NatSub
  VERINA58GetD
  VERINA58SnocGraph VERINA58Snoc
  VERINA58Min VERINA58NextValue VERINA58NextUgly
  VERINA58State VERINA58Step
  VERINA58LoopGraph VERINA58Loop
  VERINA58OneWord VERINA58NthUglyNumber
  VERINA58DivideOutGraph VERINA58DivideOut
  VERINA58IsUgly VERINA58UglyCount
  VERINA58Pre VERINA58Post
$.

verina58-nat-sub-syntax
  $a class ( VERINA58NatSub A B ) $.
verina58-get-default-syntax
  $a class ( VERINA58GetD A B ) $.
verina58-snoc-graph-syntax
  $a wff ( VERINA58SnocGraph A B C ) $.
verina58-snoc-syntax
  $a class ( VERINA58Snoc A B ) $.
verina58-min-syntax
  $a class ( VERINA58Min A B ) $.
verina58-next-value-syntax
  $a class ( VERINA58NextValue A B C D ) $.
verina58-next-ugly-syntax
  $a class ( VERINA58NextUgly A B C D ) $.
verina58-state-syntax
  $a class VERINA58State $.
verina58-step-syntax
  $a class ( VERINA58Step A ) $.
verina58-loop-graph-syntax
  $a wff ( VERINA58LoopGraph A B C D E F ) $.
verina58-loop-syntax
  $a class ( VERINA58Loop A B C D E ) $.
verina58-one-word-syntax
  $a class VERINA58OneWord $.
verina58-nth-ugly-number-syntax
  $a class ( VERINA58NthUglyNumber A ) $.
verina58-divide-out-graph-syntax
  $a wff ( VERINA58DivideOutGraph A B C ) $.
verina58-divide-out-syntax
  $a class ( VERINA58DivideOut A B ) $.
verina58-is-ugly-syntax
  $a class ( VERINA58IsUgly A ) $.
verina58-ugly-count-syntax
  $a class ( VERINA58UglyCount A ) $.
verina58-precondition-syntax
  $a wff ( VERINA58Pre A ) $.
verina58-postcondition-syntax
  $a wff ( VERINA58Post A B ) $.

verina58-nat-sub-definition $a |- (
  VERINA58NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verina58-get-default-definition $a |- (
  VERINA58GetD A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C $.

  verina58-snoc-graph-definition $a |- (
    VERINA58SnocGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. Word NN0
    )
    /\
    (
      ( # ` C ) = ( ( # ` A ) + 1 )
      /\
      (
        A. k e. ( 0 ..^ ( # ` A ) )
          ( C ` k ) = ( A ` k )
        /\
        ( C ` ( # ` A ) ) = B
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina58-snoc-definition $a |- (
    VERINA58Snoc A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA58SnocGraph A B y )
  ) $.
$}

verina58-min-definition $a |- (
  VERINA58Min A B
) = if (
  A < B ,
  A ,
  B
) $.

verina58-next-value-definition $a |- (
  VERINA58NextValue A B C D
) = (
  VERINA58Min
    ( ( VERINA58GetD A B ) x. 2 )
    (
      VERINA58Min
        ( ( VERINA58GetD A C ) x. 3 )
        ( ( VERINA58GetD A D ) x. 5 )
    )
) $.

verina58-next-ugly-definition $a |- (
  VERINA58NextUgly A B C D
) = <.
  ( VERINA58NextValue A B C D )
  ,
  <.
    if (
      ( VERINA58NextValue A B C D )
        = ( ( VERINA58GetD A B ) x. 2 ) ,
      ( B + 1 ) ,
      B
    )
    ,
    <.
      if (
        ( VERINA58NextValue A B C D )
          = ( ( VERINA58GetD A C ) x. 3 ) ,
        ( C + 1 ) ,
        C
      )
      ,
      if (
        ( VERINA58NextValue A B C D )
          = ( ( VERINA58GetD A D ) x. 5 ) ,
        ( D + 1 ) ,
        D
      )
    >.
  >.
>. $.

verina58-state-definition $a |- VERINA58State = (
  Word NN0 X. ( NN0 X. ( NN0 X. NN0 ) )
) $.

verina58-step-definition $a |- (
  VERINA58Step A
) = <.
  (
    VERINA58Snoc
      ( 1st ` A )
      (
        1st ` (
          VERINA58NextUgly
            ( 1st ` A )
            ( 1st ` ( 2nd ` A ) )
            ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
            ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
        )
      )
  )
  ,
  <.
    (
      1st ` (
        2nd ` (
          VERINA58NextUgly
            ( 1st ` A )
            ( 1st ` ( 2nd ` A ) )
            ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
            ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
        )
      )
    )
    ,
    <.
      (
        1st ` (
          2nd ` (
            2nd ` (
              VERINA58NextUgly
                ( 1st ` A )
                ( 1st ` ( 2nd ` A ) )
                ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
                ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
            )
          )
        )
      )
      ,
      (
        2nd ` (
          2nd ` (
            2nd ` (
              VERINA58NextUgly
                ( 1st ` A )
                ( 1st ` ( 2nd ` A ) )
                ( 1st ` ( 2nd ` ( 2nd ` A ) ) )
                ( 2nd ` ( 2nd ` ( 2nd ` A ) ) )
            )
          )
        )
      )
    >.
  >.
>. $.

${
  $d k t A B C D E F $.

  verina58-loop-graph-definition $a |- (
    VERINA58LoopGraph A B C D E F
  ) <-> (
    (
      (
        (
          (
            (
              A e. NN0
              /\
              B e. Word NN0
            )
            /\
            C e. NN0
          )
          /\
          D e. NN0
        )
        /\
        E e. NN0
      )
      /\
      F e. Word NN0
    )
    /\
    E. t e. Word VERINA58State
      (
        (
          ( # ` t ) = ( A + 1 )
          /\
          ( t ` 0 ) = <. B , <. C , <. D , E >. >. >.
        )
        /\
        (
          A. k e. ( 0 ..^ A )
            ( t ` ( k + 1 ) ) = ( VERINA58Step ( t ` k ) )
          /\
          F = ( 1st ` ( t ` A ) )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verina58-loop-definition $a |- (
    VERINA58Loop A B C D E
  ) = (
    iota_ y e. Word NN0
      ( VERINA58LoopGraph A B C D E y )
  ) $.
$}

verina58-one-word-definition $a |- VERINA58OneWord = (
  iota_ y e. Word NN0
    (
      ( # ` y ) = 1
      /\
      ( y ` 0 ) = 1
    )
) $.

verina58-nth-ugly-number-definition $a |- (
  VERINA58NthUglyNumber A
) = (
  VERINA58GetD
    (
      VERINA58Loop
        ( VERINA58NatSub A 1 )
        VERINA58OneWord
        0
        0
        0
    )
    ( VERINA58NatSub A 1 )
) $.

${
  $d e r A B C $.

  verina58-divide-out-graph-definition $a |- (
    VERINA58DivideOutGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. NN0
      )
      /\
      C e. NN0
    )
    /\
    (
      (
        (
          0 < A
          /\
          1 < B
        )
        /\
        E. e e. NN0 E. r e. NN0
          (
            (
              A = ( ( B ^ e ) x. r )
              /\
              ( r mod B ) =/= 0
            )
            /\
            C = r
          )
      )
      \/
      (
        -.
        (
          0 < A
          /\
          1 < B
        )
        /\
        C = A
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina58-divide-out-definition $a |- (
    VERINA58DivideOut A B
  ) = (
    iota_ y e. NN0
      ( VERINA58DivideOutGraph A B y )
  ) $.
$}

verina58-is-ugly-definition $a |- (
  VERINA58IsUgly A
) = if (
  A = 0 ,
  0 ,
  if (
    (
      VERINA58DivideOut
        (
          VERINA58DivideOut
            ( VERINA58DivideOut A 2 )
            3
        )
        5
    ) = 1 ,
    1 ,
    0
  )
) $.

${
  $d i A $.

  verina58-ugly-count-definition $a |- (
    VERINA58UglyCount A
  ) = (
    # ` {
      i e. ( 0 ..^ A )
      |
      ( VERINA58IsUgly i ) = 1
    }
  ) $.
$}

verina58-precondition-definition $a |- (
  VERINA58Pre A
) <-> (
  A e. NN0
  /\
  0 < A
) $.

verina58-postcondition-definition $a |- (
  VERINA58Post A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    ( VERINA58IsUgly B ) = 1
    /\
    (
      VERINA58UglyCount B
    ) = (
      VERINA58NatSub A 1
    )
  )
) $.

verina-advanced-58-nth-ugly-number $a |- A. n e. NN0
  (
    ( VERINA58Pre n )
    ->
    (
      VERINA58Post
        n
        ( VERINA58NthUglyNumber n )
    )
  )
$.
