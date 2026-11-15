$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_52 (verina__metamath__verina_advanced_52), catalog title
  minOperations: the exact reverse-list scan counts removals from the end of
  an arbitrary finite natural-number list until every target from one through
  k has been collected, and satisfies the stated minimum-operations
  specification. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` i is zero-based lookup, ran w is its membership
  set, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA52ConsGraph and VERINA52Cons are exact list cons.
  VERINA52Relevant is the source test that a head is positive, at most k, and
  absent from the collected list. VERINA52State is the exact loop state type
  consisting of the collected list, collected_count, and ops.
  VERINA52LoopStep performs one source loop iteration, including incrementing
  ops on every nonempty remaining list and updating the collected list and
  count exactly when the head is relevant. VERINA52LoopHit is exactly the
  branch where that relevant insertion makes collected_count equal k.

  VERINA52LoopGraph records the unique state trace from all five arbitrary
  helper arguments. It stops after the first hitting iteration or after all
  remaining entries have been processed, exactly matching both recursive
  branches and the empty-list return. VERINA52Loop selects its unique result.
  VERINA52Reverse is exact List.reverse, and VERINA52MinOperations preserves
  the source k = 0 branch and otherwise invokes the helper on the reversed
  input with the empty collection and zero counters. Thus the implementation
  is fixed independently of the postcondition.

  VERINA52Pre says that the typed input contains every natural number from
  one through k, exactly the mapped List.range/all precondition, including
  its vacuous k = 0 case. VERINA52NatSub restores Lean's truncated Nat.sub,
  and VERINA52Take is exact List.take. VERINA52Post says that the first result
  elements of the reversed input contain every target and that either one
  fewer element does not suffice when the result is positive, or k is zero
  when the result is zero. The proof-valued precondition arguments are
  computationally and propositionally unused and are omitted. The final $a
  declaration is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA52ConsGraph VERINA52Cons
  VERINA52Relevant VERINA52State
  VERINA52LoopStep VERINA52LoopHit
  VERINA52LoopGraph VERINA52Loop
  VERINA52ReverseGraph VERINA52Reverse
  VERINA52MinOperations
  VERINA52Pre
  VERINA52NatSub
  VERINA52TakeGraph VERINA52Take
  VERINA52Post
$.

verina52-cons-graph-syntax
  $a wff ( VERINA52ConsGraph A B C ) $.
verina52-cons-syntax
  $a class ( VERINA52Cons A B ) $.
verina52-relevant-syntax
  $a wff ( VERINA52Relevant A B C ) $.
verina52-state-syntax
  $a class VERINA52State $.
verina52-loop-step-syntax
  $a wff ( VERINA52LoopStep A B C D ) $.
verina52-loop-hit-syntax
  $a wff ( VERINA52LoopHit A B C ) $.
verina52-loop-graph-syntax
  $a wff ( VERINA52LoopGraph A B C D E F ) $.
verina52-loop-syntax
  $a class ( VERINA52Loop A B C D E ) $.
verina52-reverse-graph-syntax
  $a wff ( VERINA52ReverseGraph A B ) $.
verina52-reverse-syntax
  $a class ( VERINA52Reverse A ) $.
verina52-min-operations-syntax
  $a class ( VERINA52MinOperations A B ) $.
verina52-precondition-syntax
  $a wff ( VERINA52Pre A B ) $.
verina52-nat-sub-syntax
  $a class ( VERINA52NatSub A B ) $.
verina52-take-graph-syntax
  $a wff ( VERINA52TakeGraph A B C ) $.
verina52-take-syntax
  $a class ( VERINA52Take A B ) $.
verina52-postcondition-syntax
  $a wff ( VERINA52Post A B C ) $.

${
  $d j A B C $.

  verina52-cons-graph-definition $a |- (
    VERINA52ConsGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. Word NN0
      )
      /\
      C e. Word NN0
    )
    /\
    (
      ( # ` C ) = ( ( # ` B ) + 1 )
      /\
      (
        ( C ` 0 ) = A
        /\
        A. j e. ( 0 ..^ ( # ` B ) )
          ( C ` ( j + 1 ) ) = ( B ` j )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina52-cons-definition $a |- (
    VERINA52Cons A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA52ConsGraph A B y )
  ) $.
$}

verina52-relevant-definition $a |- (
  VERINA52Relevant A B C
) <-> (
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
  (
    (
      0 < A
      /\
      A <_ C
    )
    /\
    -. ( A e. ran B )
  )
) $.

verina52-state-definition $a |- VERINA52State =
  ( Word NN0 X. ( NN0 X. NN0 ) ) $.

verina52-loop-step-definition $a |- (
  VERINA52LoopStep A B C D
) <-> (
  (
    (
      (
        A e. NN0
        /\
        B e. VERINA52State
      )
      /\
      C e. NN0
    )
    /\
    D e. VERINA52State
  )
  /\
  (
    (
      2nd ` ( 2nd ` D )
    ) = (
      ( 2nd ` ( 2nd ` B ) ) + 1
    )
    /\
    (
      (
        ( VERINA52Relevant A ( 1st ` B ) C )
        /\
        (
          (
            1st ` D
          ) = (
            VERINA52Cons A ( 1st ` B )
          )
          /\
          (
            1st ` ( 2nd ` D )
          ) = (
            ( 1st ` ( 2nd ` B ) ) + 1
          )
        )
      )
      \/
      (
        -. ( VERINA52Relevant A ( 1st ` B ) C )
        /\
        (
          (
            1st ` D
          ) = (
            1st ` B
          )
          /\
          (
            1st ` ( 2nd ` D )
          ) = (
            1st ` ( 2nd ` B )
          )
        )
      )
    )
  )
) $.

verina52-loop-hit-definition $a |- (
  VERINA52LoopHit A B C
) <-> (
  (
    (
      A e. NN0
      /\
      B e. VERINA52State
    )
    /\
    C e. NN0
  )
  /\
  (
    ( VERINA52Relevant A ( 1st ` B ) C )
    /\
    (
      ( 1st ` ( 2nd ` B ) ) + 1
    ) = C
  )
) $.

${
  $d j s t A B C D E F $.

  verina52-loop-graph-definition $a |- (
    VERINA52LoopGraph A B C D E F
  ) <-> (
    (
      (
        (
          A e. Word NN0
          /\
          B e. Word NN0
        )
        /\
        (
          C e. NN0
          /\
          D e. NN0
        )
      )
      /\
      (
        E e. NN0
        /\
        F e. NN0
      )
    )
    /\
    E. s e. NN0
      E. t e. Word VERINA52State
        (
          (
            (
              s <_ ( # ` A )
              /\
              ( # ` t ) = ( s + 1 )
            )
            /\
            (
              t ` 0
            ) = <. B , <. C , D >. >.
          )
          /\
          (
            (
              A. j e. ( 0 ..^ s )
                (
                  (
                    VERINA52LoopStep
                      ( A ` j )
                      ( t ` j )
                      E
                      ( t ` ( j + 1 ) )
                  )
                  /\
                  (
                    ( j + 1 ) < s
                    ->
                    -.
                    (
                      VERINA52LoopHit
                        ( A ` j )
                        ( t ` j )
                        E
                    )
                  )
                )
              /\
              (
                s = ( # ` A )
                \/
                (
                  0 < s
                  /\
                  (
                    VERINA52LoopHit
                      ( A ` ( s - 1 ) )
                      ( t ` ( s - 1 ) )
                      E
                  )
                )
              )
            )
            /\
            F = ( 2nd ` ( 2nd ` ( t ` s ) ) )
          )
        )
  ) $.
$}

${
  $d y A B C D E $.

  verina52-loop-definition $a |- (
    VERINA52Loop A B C D E
  ) = (
    iota_ y e. NN0
      ( VERINA52LoopGraph A B C D E y )
  ) $.
$}

${
  $d i A B $.

  verina52-reverse-graph-definition $a |- (
    VERINA52ReverseGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. Word NN0
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` i
        ) = (
          A ` ( ( ( # ` A ) - 1 ) - i )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina52-reverse-definition $a |- (
    VERINA52Reverse A
  ) = (
    iota_ y e. Word NN0
      ( VERINA52ReverseGraph A y )
  ) $.
$}

verina52-min-operations-definition $a |- (
  VERINA52MinOperations A B
) = if (
  B = 0 ,
  0 ,
  (
    VERINA52Loop
      ( VERINA52Reverse A )
      (/)
      0
      0
      B
  )
) $.

${
  $d n A B $.

  verina52-precondition-definition $a |- (
    VERINA52Pre A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    A. n e. ( 1 ..^ ( B + 1 ) )
      n e. ran A
  ) $.
$}

verina52-nat-sub-definition $a |- (
  VERINA52NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d i A B C $.

  verina52-take-graph-definition $a |- (
    VERINA52TakeGraph A B C
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
      ( # ` C ) = if (
        B < ( # ` A ) ,
        B ,
        ( # ` A )
      )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        ( C ` i ) = ( A ` i )
    )
  ) $.
$}

${
  $d y A B $.

  verina52-take-definition $a |- (
    VERINA52Take A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA52TakeGraph A B y )
  ) $.
$}

${
  $d n A B C $.

  verina52-postcondition-definition $a |- (
    VERINA52Post A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. NN0
    )
    /\
    (
      A. n e. ( 1 ..^ ( B + 1 ) )
        n e. ran
          ( VERINA52Take ( VERINA52Reverse A ) C )
      /\
      (
        (
          0 < C
          /\
          -.
          (
            A. n e. ( 1 ..^ ( B + 1 ) )
              n e. ran
                (
                  VERINA52Take
                    ( VERINA52Reverse A )
                    ( VERINA52NatSub C 1 )
                )
          )
        )
        \/
        (
          C = 0
          /\
          B = 0
        )
      )
    )
  ) $.
$}

verina-advanced-52-min-operations
  $a |- A. w e. Word NN0
    A. k e. NN0
      (
        ( VERINA52Pre w k )
        ->
        (
          VERINA52Post
            w
            k
            ( VERINA52MinOperations w k )
        )
      )
  $.
