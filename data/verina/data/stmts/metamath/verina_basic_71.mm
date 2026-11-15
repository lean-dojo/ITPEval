$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_71
  (verina__metamath__verina_basic_71), catalog title LongestCommonPrefix: the
  exact executable character-list scan accumulates equal leading characters
  until the first mismatch or the end of the shorter input and satisfies the
  maximal common-prefix correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB71Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB71Char is exactly the type of arbitrary finite List Char
  values. For a word w, # ` w is its natural-number length, w ` i is
  zero-based lookup, (/) is the empty list, <" c "> is the singleton list,
  and ++ is exact List.append.

  VERINAB71None, VERINAB71Some, VERINAB71OptionChar, and
  VERINAB71GetOption reproduce List.get? exactly, including none outside the
  valid index range. VERINAB71NatMin is natural minimum.

  VERINAB71AuxContinue is exactly the recursive branch of the local aux
  helper where idx is below minLength, both lookups are some of the same
  character, and that character is appended to acc while idx increases by
  one. VERINAB71AuxStop is exactly every return-acc branch: idx has reached
  minLength, the two options differ, or both are none. VERINAB71AuxGraph
  records the complete finite execution trace from arbitrary typed idx and
  acc arguments, and VERINAB71Aux selects its unique result.

  VERINAB71LongestCommonPrefix computes minLength from the two input lengths
  and calls the exact helper at index zero with the empty accumulator. Thus
  the executable output is fixed independently of the postcondition and the
  graph admits no additional results.

  VERINAB71TakeGraph and VERINAB71Take reproduce List.take for every natural
  length, including clipping at the input length. VERINAB71Pre is the source
  True precondition together with the two List Char input types.
  VERINAB71Post preserves all five source clauses: both length bounds, both
  take equalities, and termination because the result reaches an input end or
  the two next option-valued characters differ. The proof-valued precondition
  arguments are computationally and propositionally unused and are
  represented by the explicit precondition antecedent of the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c
  VERINAB71Char
  VERINAB71None VERINAB71Some VERINAB71OptionChar VERINAB71GetOption
  VERINAB71NatMin
  VERINAB71AuxContinue VERINAB71AuxStop
  VERINAB71AuxGraph VERINAB71Aux
  VERINAB71TakeGraph VERINAB71Take
  VERINAB71Pre VERINAB71LongestCommonPrefix VERINAB71Post
$.

verinab71-char-syntax
  $a class VERINAB71Char $.
verinab71-none-syntax
  $a class VERINAB71None $.
verinab71-some-syntax
  $a class ( VERINAB71Some A ) $.
verinab71-option-char-syntax
  $a class VERINAB71OptionChar $.
verinab71-get-option-syntax
  $a class ( VERINAB71GetOption A B ) $.
verinab71-nat-min-syntax
  $a class ( VERINAB71NatMin A B ) $.
verinab71-aux-continue-syntax
  $a wff ( VERINAB71AuxContinue A B C D E ) $.
verinab71-aux-stop-syntax
  $a wff ( VERINAB71AuxStop A B C D E ) $.
verinab71-aux-graph-syntax
  $a wff ( VERINAB71AuxGraph A B C D E F ) $.
verinab71-aux-syntax
  $a class ( VERINAB71Aux A B C D E ) $.
verinab71-take-graph-syntax
  $a wff ( VERINAB71TakeGraph A B C ) $.
verinab71-take-syntax
  $a class ( VERINAB71Take A B ) $.
verinab71-precondition-syntax
  $a wff ( VERINAB71Pre A B ) $.
verinab71-program-syntax
  $a class ( VERINAB71LongestCommonPrefix A B ) $.
verinab71-postcondition-syntax
  $a wff ( VERINAB71Post A B C ) $.

verinab71-char-definition $a |- VERINAB71Char =
  { x e. NN0 |
    (
      x < ; ; ; ; ; ; 1 1 1 4 1 1 2
      /\
      (
        x < ; ; ; ; 5 5 2 9 6
        \/
        ; ; ; ; 5 7 3 4 3 < x
      )
    )
  } $.

verinab71-none-definition $a |- VERINAB71None = (/) $.

verinab71-some-definition $a |- (
  VERINAB71Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verinab71-option-char-definition $a |- VERINAB71OptionChar =
    { x |
      (
        x = VERINAB71None
        \/
        E. y e. VERINAB71Char
          x = ( VERINAB71Some y )
      )
    } $.
$}

verinab71-get-option-definition $a |- (
  VERINAB71GetOption A B
) = if (
  B < ( # ` A ) ,
  ( VERINAB71Some ( A ` B ) ) ,
  VERINAB71None
) $.

verinab71-nat-min-definition $a |- (
  VERINAB71NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

${
  $d A B C D E $.

  verinab71-aux-continue-definition $a |- (
    VERINAB71AuxContinue A B C D E
  ) <-> (
    (
      (
        (
          A e. Word VERINAB71Char
          /\
          B e. Word VERINAB71Char
        )
        /\
        C e. NN0
      )
      /\
      (
        D e. ( NN0 X. Word VERINAB71Char )
        /\
        E e. ( NN0 X. Word VERINAB71Char )
      )
    )
    /\
    (
      (
        ( 1st ` D ) < C
        /\
        (
          VERINAB71GetOption A ( 1st ` D )
        ) = (
          VERINAB71Some ( A ` ( 1st ` D ) )
        )
      )
      /\
      (
        (
          VERINAB71GetOption B ( 1st ` D )
        ) = (
          VERINAB71GetOption A ( 1st ` D )
        )
        /\
        E = <.
          ( ( 1st ` D ) + 1 ) ,
          (
            ( 2nd ` D )
            ++
            <" ( A ` ( 1st ` D ) ) ">
          )
        >.
      )
    )
  ) $.
$}

${
  $d A B C D E $.

  verinab71-aux-stop-definition $a |- (
    VERINAB71AuxStop A B C D E
  ) <-> (
    (
      (
        (
          A e. Word VERINAB71Char
          /\
          B e. Word VERINAB71Char
        )
        /\
        C e. NN0
      )
      /\
      (
        D e. ( NN0 X. Word VERINAB71Char )
        /\
        E e. Word VERINAB71Char
      )
    )
    /\
    (
      E = ( 2nd ` D )
      /\
      (
        C <_ ( 1st ` D )
        \/
        (
          ( 1st ` D ) < C
          /\
          (
            (
              VERINAB71GetOption A ( 1st ` D )
            ) =/= (
              VERINAB71GetOption B ( 1st ` D )
            )
            \/
            (
              VERINAB71GetOption A ( 1st ` D )
            ) = VERINAB71None
          )
        )
      )
    )
  ) $.
$}

${
  $d i k t A B C D E F $.

  verinab71-aux-graph-definition $a |- (
    VERINAB71AuxGraph A B C D E F
  ) <-> (
    (
      (
        (
          (
            A e. Word VERINAB71Char
            /\
            B e. Word VERINAB71Char
          )
          /\
          C e. NN0
        )
        /\
        D e. NN0
      )
      /\
      (
        E e. Word VERINAB71Char
        /\
        F e. Word VERINAB71Char
      )
    )
    /\
    E. k e. NN0
      E. t e. Word ( NN0 X. Word VERINAB71Char )
        (
          (
            ( # ` t ) = ( k + 1 )
            /\
            ( t ` 0 ) = <. D , E >.
          )
          /\
          (
            A. i e. ( 0 ..^ k )
              (
                VERINAB71AuxContinue
                  A
                  B
                  C
                  ( t ` i )
                  ( t ` ( i + 1 ) )
              )
            /\
            (
              VERINAB71AuxStop
                A
                B
                C
                ( t ` k )
                F
            )
          )
        )
  ) $.
$}

${
  $d y A B C D E $.

  verinab71-aux-definition $a |- (
    VERINAB71Aux A B C D E
  ) = (
    iota_ y e. Word VERINAB71Char
      ( VERINAB71AuxGraph A B C D E y )
  ) $.
$}

${
  $d i A B C $.

  verinab71-take-graph-definition $a |- (
    VERINAB71TakeGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINAB71Char
        /\
        B e. NN0
      )
      /\
      C e. Word VERINAB71Char
    )
    /\
    (
      ( # ` C ) = (
        VERINAB71NatMin B ( # ` A )
      )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        ( C ` i ) = ( A ` i )
    )
  ) $.
$}

${
  $d y A B $.

  verinab71-take-definition $a |- (
    VERINAB71Take A B
  ) = (
    iota_ y e. Word VERINAB71Char
      ( VERINAB71TakeGraph A B y )
  ) $.
$}

verinab71-precondition-definition $a |- (
  VERINAB71Pre A B
) <-> (
  A e. Word VERINAB71Char
  /\
  B e. Word VERINAB71Char
) $.

verinab71-program-definition $a |- (
  VERINAB71LongestCommonPrefix A B
) = (
  VERINAB71Aux
    A
    B
    (
      VERINAB71NatMin
        ( # ` A )
        ( # ` B )
    )
    0
    (/)
) $.

verinab71-postcondition-definition $a |- (
  VERINAB71Post A B C
) <-> (
  (
    (
      A e. Word VERINAB71Char
      /\
      B e. Word VERINAB71Char
    )
    /\
    C e. Word VERINAB71Char
  )
  /\
  (
    ( # ` C ) <_ ( # ` A )
    /\
    (
      C = ( VERINAB71Take A ( # ` C ) )
      /\
      (
        ( # ` C ) <_ ( # ` B )
        /\
        (
          C = ( VERINAB71Take B ( # ` C ) )
          /\
          (
            ( # ` C ) = ( # ` A )
            \/
            (
              ( # ` C ) = ( # ` B )
              \/
              (
                VERINAB71GetOption A ( # ` C )
              ) =/= (
                VERINAB71GetOption B ( # ` C )
              )
            )
          )
        )
      )
    )
  )
) $.

verina-basic-71-longest-common-prefix $a |-
  A. a e. Word VERINAB71Char
    A. b e. Word VERINAB71Char
      (
        ( VERINAB71Pre a b )
        ->
        (
          VERINAB71Post
            a
            b
            ( VERINAB71LongestCommonPrefix a b )
        )
      )
$.
