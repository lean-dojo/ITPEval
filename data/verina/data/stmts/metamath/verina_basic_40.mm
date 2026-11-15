$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_40
  (verina__metamath__verina_basic_40), catalog title secondSmallest: the exact
  executable indexed scan of an integer array with at least two distinct
  values returns its second-smallest distinct value and satisfies the complete
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB40GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB40NatSub is
  Lean's truncated natural subtraction. VERINAB40None and VERINAB40Some give
  a disjoint tagged representation of Option Nat, and VERINAB40OptionGetD
  extracts the stored natural or returns zero for none.

  VERINAB40State is the exact helper state
    (current index, minimum index, optional second-minimum index).
  VERINAB40Step reproduces one nonterminal branch of secondSmallestAux:
  it advances the current index, updates the minimum index when the current
  value is smaller, initializes the second index on the first distinct larger
  value, and otherwise replaces it exactly when the current value lies
  strictly between the tracked minimum and second value.

  VERINAB40AuxGraph records the complete deterministic helper execution.
  Starting from arbitrary typed helper arguments, its trace has exactly
  s.size - i updates, so its final state is the first one whose current index
  is at least s.size. VERINAB40Finish returns the entry at the stored second
  index, or zero for none, exactly reproducing the source terminal match and
  the inhabited integer result of its panic branch. VERINAB40SecondSmallestAux
  selects the unique graph result, and VERINAB40SecondSmallest invokes it with
  source initial state (1, 0, none). Thus the executable result is fixed
  independently of the postcondition and the graph admits no extra outputs.

  VERINAB40Pre preserves the source size and distinct-entry assumptions.
  VERINAB40Post preserves both source existential clauses and the universal
  lower-bound condition over every valid array index. The proof-valued
  precondition arguments to the implementation and postcondition have no
  computational or propositional effect beyond the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB40GetBang VERINAB40NatSub
  VERINAB40None VERINAB40Some VERINAB40OptionNat VERINAB40OptionGetD
  VERINAB40State VERINAB40Step VERINAB40Finish
  VERINAB40AuxGraph VERINAB40SecondSmallestAux
  VERINAB40Pre VERINAB40SecondSmallest VERINAB40Post
$.

verinab40-get-bang-syntax
  $a class ( VERINAB40GetBang A B ) $.
verinab40-nat-sub-syntax
  $a class ( VERINAB40NatSub A B ) $.
verinab40-none-syntax
  $a class VERINAB40None $.
verinab40-some-syntax
  $a class ( VERINAB40Some A ) $.
verinab40-option-nat-syntax
  $a class VERINAB40OptionNat $.
verinab40-option-get-d-syntax
  $a class ( VERINAB40OptionGetD A ) $.
verinab40-state-syntax
  $a class VERINAB40State $.
verinab40-step-syntax
  $a class ( VERINAB40Step A B ) $.
verinab40-finish-syntax
  $a class ( VERINAB40Finish A B ) $.
verinab40-aux-graph-syntax
  $a wff ( VERINAB40AuxGraph A B C D E ) $.
verinab40-aux-syntax
  $a class ( VERINAB40SecondSmallestAux A B C D ) $.
verinab40-precondition-syntax
  $a wff ( VERINAB40Pre A ) $.
verinab40-program-syntax
  $a class ( VERINAB40SecondSmallest A ) $.
verinab40-postcondition-syntax
  $a wff ( VERINAB40Post A B ) $.

verinab40-get-bang-definition $a |- (
  VERINAB40GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab40-nat-sub-definition $a |- (
  VERINAB40NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab40-none-definition $a |- VERINAB40None = (/) $.

verinab40-some-definition $a |- (
  VERINAB40Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verinab40-option-nat-definition $a |- VERINAB40OptionNat =
    { x |
      (
        x = VERINAB40None
        \/
        E. y e. NN0
          x = ( VERINAB40Some y )
      )
    } $.
$}

${
  $d y A $.

  verinab40-option-get-d-definition $a |- (
    VERINAB40OptionGetD A
  ) = if (
    A = VERINAB40None ,
    0 ,
    iota_ y e. NN0
      A = ( VERINAB40Some y )
  ) $.
$}

verinab40-state-definition $a |- VERINAB40State = (
  NN0 X. ( NN0 X. VERINAB40OptionNat )
) $.

verinab40-step-definition $a |- (
  VERINAB40Step A B
) = <.
  ( ( 1st ` B ) + 1 )
  ,
  <.
    if (
      (
        VERINAB40GetBang A ( 1st ` B )
      ) < (
        VERINAB40GetBang A ( 1st ` ( 2nd ` B ) )
      ) ,
      ( 1st ` B ) ,
      ( 1st ` ( 2nd ` B ) )
    )
    ,
    if (
      (
        VERINAB40GetBang A ( 1st ` B )
      ) < (
        VERINAB40GetBang A ( 1st ` ( 2nd ` B ) )
      ) ,
      (
        VERINAB40Some
          ( 1st ` ( 2nd ` B ) )
      ) ,
      if (
        ( 2nd ` ( 2nd ` B ) ) = VERINAB40None ,
        if (
          (
            VERINAB40GetBang A ( 1st ` ( 2nd ` B ) )
          ) < (
            VERINAB40GetBang A ( 1st ` B )
          ) ,
          ( VERINAB40Some ( 1st ` B ) ) ,
          VERINAB40None
        ) ,
        if (
          (
            (
              VERINAB40GetBang A ( 1st ` B )
            ) < (
              VERINAB40GetBang
                A
                (
                  VERINAB40OptionGetD
                    ( 2nd ` ( 2nd ` B ) )
                )
            )
            /\
            (
              VERINAB40GetBang A ( 1st ` ( 2nd ` B ) )
            ) < (
              VERINAB40GetBang A ( 1st ` B )
            )
          ) ,
          ( VERINAB40Some ( 1st ` B ) ) ,
          ( 2nd ` ( 2nd ` B ) )
        )
      )
    )
  >.
>. $.

verinab40-finish-definition $a |- (
  VERINAB40Finish A B
) = if (
  ( 2nd ` ( 2nd ` B ) ) = VERINAB40None ,
  0 ,
  (
    VERINAB40GetBang
      A
      (
        VERINAB40OptionGetD
          ( 2nd ` ( 2nd ` B ) )
      )
  )
) $.

${
  $d k t A B C D E $.

  verinab40-aux-graph-definition $a |- (
    VERINAB40AuxGraph A B C D E
  ) <-> (
    (
      (
        (
          (
            A e. Word ZZ
            /\
            B e. NN0
          )
          /\
          C e. NN0
        )
        /\
        D e. VERINAB40OptionNat
      )
      /\
      E e. ZZ
    )
    /\
    E. t e. Word VERINAB40State
      (
        (
          ( # ` t ) = (
            ( VERINAB40NatSub ( # ` A ) B ) + 1
          )
          /\
          ( t ` 0 ) = <. B , <. C , D >. >.
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB40NatSub ( # ` A ) B )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB40Step A ( t ` k )
            )
          /\
          E = (
            VERINAB40Finish
              A
              (
                t ` (
                  VERINAB40NatSub ( # ` A ) B
                )
              )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D $.

  verinab40-aux-definition $a |- (
    VERINAB40SecondSmallestAux A B C D
  ) = (
    iota_ y e. ZZ
      ( VERINAB40AuxGraph A B C D y )
  ) $.
$}

${
  $d i j A $.

  verinab40-precondition-definition $a |- (
    VERINAB40Pre A
  ) <-> (
    A e. Word ZZ
    /\
    (
      1 < ( # ` A )
      /\
      E. i e. NN0 E. j e. NN0
        (
          (
            i < ( # ` A )
            /\
            j < ( # ` A )
          )
          /\
          (
            VERINAB40GetBang A i
          ) =/= (
            VERINAB40GetBang A j
          )
        )
    )
  ) $.
$}

verinab40-program-definition $a |- (
  VERINAB40SecondSmallest A
) = (
  VERINAB40SecondSmallestAux
    A
    1
    0
    VERINAB40None
) $.

${
  $d i j k A B $.

  verinab40-postcondition-definition $a |- (
    VERINAB40Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      E. i e. NN0
        (
          i < ( # ` A )
          /\
          ( VERINAB40GetBang A i ) = B
        )
      /\
      E. j e. NN0
        (
          j < ( # ` A )
          /\
          (
            ( VERINAB40GetBang A j ) < B
            /\
            A. k e. NN0
              (
                k < ( # ` A )
                ->
                (
                  (
                    VERINAB40GetBang A k
                  ) =/= (
                    VERINAB40GetBang A j
                  )
                  ->
                  B <_ ( VERINAB40GetBang A k )
                )
              )
          )
        )
    )
  ) $.
$}

verina-basic-40-second-smallest $a |- A. s e. Word ZZ
  (
    ( VERINAB40Pre s )
    ->
    (
      VERINAB40Post
        s
        ( VERINAB40SecondSmallest s )
    )
  )
$.
