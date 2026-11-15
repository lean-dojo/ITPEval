$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_26 (verina__metamath__verina_advanced_26), catalog title
  letterCombinations: the exact recursive telephone-keypad combination
  program and its independently folded output contract for arbitrary Unicode
  input strings. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA26Char is exactly Lean's Char domain of Unicode scalar values, so
  Word VERINA26Char represents arbitrary strings extensionally through
  String.toList. VERINA26DigitBase and VERINA26DigitLength encode the source
  digitToLetters table for characters 2 through 9, including the four-letter
  entries for 7 and 9; all other characters map to the empty word.

  VERINA26PrependGraph is the exact source branch that maps each current
  letter to a singleton string when the recursive tail result is empty, and
  otherwise flatMaps current letters in order over the tail combinations,
  prepending the current letter to every tail string. VERINA26GoGraph records
  the structurally recursive go computation from the empty suffix back
  through the input. VERINA26LetterCombinations first performs the source
  any-test for an empty digit mapping and returns the empty list on failure;
  otherwise it selects the unique go result. It is therefore the executable
  implementation, not an output chosen from the postcondition.

  VERINA26ExpectedStepGraph separately reproduces the postcondition's foldl:
  starting with the singleton list containing the empty string, it flatMaps
  each accumulated prefix in order over the next digit's letters and appends
  one character. VERINA26Expected selects that exact ordered fold result.
  VERINA26Pre is the source True precondition together with the String input
  type. VERINA26Post preserves the empty-input and invalid-character branches,
  then states the source length equality and both List.all membership tests.
  The proof-valued precondition argument is computationally and
  propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and there is no $p
  declaration.
$)

$c
  VERINA26Char
  VERINA26ValidDigit
  VERINA26DigitBase VERINA26DigitLength
  VERINA26DigitToLettersGraph VERINA26DigitToLetters
  VERINA26HasInvalid
  VERINA26PrependGraph
  VERINA26GoGraph VERINA26Go
  VERINA26LetterCombinations VERINA26Pre
  VERINA26ExpectedStepGraph
  VERINA26ExpectedGraph VERINA26Expected
  VERINA26Post
$.

verina26-char-syntax
  $a class VERINA26Char $.
verina26-valid-digit-syntax
  $a wff ( VERINA26ValidDigit A ) $.
verina26-digit-base-syntax
  $a class ( VERINA26DigitBase A ) $.
verina26-digit-length-syntax
  $a class ( VERINA26DigitLength A ) $.
verina26-digit-to-letters-graph-syntax
  $a wff ( VERINA26DigitToLettersGraph A B ) $.
verina26-digit-to-letters-syntax
  $a class ( VERINA26DigitToLetters A ) $.
verina26-has-invalid-syntax
  $a wff ( VERINA26HasInvalid A ) $.
verina26-prepend-graph-syntax
  $a wff ( VERINA26PrependGraph A B C ) $.
verina26-go-graph-syntax
  $a wff ( VERINA26GoGraph A B ) $.
verina26-go-syntax
  $a class ( VERINA26Go A ) $.
verina26-letter-combinations-syntax
  $a class ( VERINA26LetterCombinations A ) $.
verina26-precondition-syntax
  $a wff ( VERINA26Pre A ) $.
verina26-expected-step-graph-syntax
  $a wff ( VERINA26ExpectedStepGraph A B C ) $.
verina26-expected-graph-syntax
  $a wff ( VERINA26ExpectedGraph A B ) $.
verina26-expected-syntax
  $a class ( VERINA26Expected A ) $.
verina26-postcondition-syntax
  $a wff ( VERINA26Post A B ) $.

verina26-char-definition $a |- VERINA26Char =
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

verina26-valid-digit-definition $a |- (
  VERINA26ValidDigit A
) <-> (
  (
    A e. VERINA26Char
    /\
    ; 5 0 <_ A
  )
  /\
  A <_ ; 5 7
) $.

verina26-digit-base-definition $a |- (
  VERINA26DigitBase A
) = if (
  A = ; 5 0 ,
  ; 9 7 ,
  if (
    A = ; 5 1 ,
    ; ; 1 0 0 ,
    if (
      A = ; 5 2 ,
      ; ; 1 0 3 ,
      if (
        A = ; 5 3 ,
        ; ; 1 0 6 ,
        if (
          A = ; 5 4 ,
          ; ; 1 0 9 ,
          if (
            A = ; 5 5 ,
            ; ; 1 1 2 ,
            if (
              A = ; 5 6 ,
              ; ; 1 1 6 ,
              if (
                A = ; 5 7 ,
                ; ; 1 1 9 ,
                0
              )
            )
          )
        )
      )
    )
  )
) $.

verina26-digit-length-definition $a |- (
  VERINA26DigitLength A
) = if (
  (
    A = ; 5 5
    \/
    A = ; 5 7
  ) ,
  4 ,
  if (
    ( VERINA26ValidDigit A ) ,
    3 ,
    0
  )
) $.

${
  $d i A B $.

  verina26-digit-to-letters-graph-definition $a |- (
    VERINA26DigitToLettersGraph A B
  ) <-> (
    (
      A e. VERINA26Char
      /\
      B e. Word VERINA26Char
    )
    /\
    (
      ( # ` B ) = ( VERINA26DigitLength A )
      /\
      A. i e. ( 0 ..^ ( # ` B ) )
        (
          B ` i
        ) = (
          ( VERINA26DigitBase A ) + i
        )
    )
  ) $.
$}

${
  $d y A $.

  verina26-digit-to-letters-definition $a |- (
    VERINA26DigitToLetters A
  ) = (
    iota_ y e. Word VERINA26Char
      ( VERINA26DigitToLettersGraph A y )
  ) $.
$}

${
  $d i A $.

  verina26-has-invalid-definition $a |- (
    VERINA26HasInvalid A
  ) <-> (
    (
      A e. Word VERINA26Char
      /\
      E. i e. ( 0 ..^ ( # ` A ) )
        -. ( VERINA26ValidDigit ( A ` i ) )
    )
  ) $.
$}

${
  $d i j q A B C $.

  verina26-prepend-graph-definition $a |- (
    VERINA26PrependGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA26Char
        /\
        B e. Word ( Word VERINA26Char )
      )
      /\
      C e. Word ( Word VERINA26Char )
    )
    /\
    (
      (
        B = (/)
        /\
        (
          ( # ` C ) = ( # ` A )
          /\
          A. q e. ( 0 ..^ ( # ` C ) )
            (
              (
                # ` ( C ` q )
              ) = 1
              /\
              (
                ( C ` q ) ` 0
              ) = (
                A ` q
              )
            )
        )
      )
      \/
      (
        B =/= (/)
        /\
        (
          ( # ` C ) = (
            ( # ` A ) x. ( # ` B )
          )
          /\
          A. q e. ( 0 ..^ ( # ` C ) )
            (
              (
                # ` ( C ` q )
              ) = (
                1 + (
                  # ` (
                    B ` ( q mod ( # ` B ) )
                  )
                )
              )
              /\
              A. j e. ( 0 ..^ ( # ` ( C ` q ) ) )
                (
                  ( C ` q ) ` j
                ) = if (
                  j = 0 ,
                  A ` (
                    |_ ` ( q / ( # ` B ) )
                  ) ,
                  (
                    B ` ( q mod ( # ` B ) )
                  ) ` ( j - 1 )
                )
            )
        )
      )
    )
  ) $.
$}

${
  $d k t A B $.

  verina26-go-graph-definition $a |- (
    VERINA26GoGraph A B
  ) <-> (
    (
      A e. Word VERINA26Char
      /\
      B e. Word ( Word VERINA26Char )
    )
    /\
    E. t e. Word ( Word ( Word VERINA26Char ) )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = (/)
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              VERINA26PrependGraph
                (
                  VERINA26DigitToLetters
                    (
                      A ` (
                        ( ( # ` A ) - 1 ) - k
                      )
                    )
                )
                ( t ` k )
                ( t ` ( k + 1 ) )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina26-go-definition $a |- (
    VERINA26Go A
  ) = (
    iota_ y e. Word ( Word VERINA26Char )
      ( VERINA26GoGraph A y )
  ) $.
$}

verina26-letter-combinations-definition $a |- (
  VERINA26LetterCombinations A
) = if (
  ( VERINA26HasInvalid A ) ,
  (/) ,
  ( VERINA26Go A )
) $.

verina26-precondition-definition $a |- (
  VERINA26Pre A
) <-> (
  A e. Word VERINA26Char
) $.

${
  $d j q A B C $.

  verina26-expected-step-graph-definition $a |- (
    VERINA26ExpectedStepGraph A B C
  ) <-> (
    (
      (
        A e. Word ( Word VERINA26Char )
        /\
        B e. Word VERINA26Char
      )
      /\
      C e. Word ( Word VERINA26Char )
    )
    /\
    (
      (
        B = (/)
        /\
        C = (/)
      )
      \/
      (
        B =/= (/)
        /\
        (
          ( # ` C ) = (
            ( # ` A ) x. ( # ` B )
          )
          /\
          A. q e. ( 0 ..^ ( # ` C ) )
            (
              (
                # ` ( C ` q )
              ) = (
                (
                  # ` (
                    A ` (
                      |_ ` ( q / ( # ` B ) )
                    )
                  )
                ) + 1
              )
              /\
              A. j e. ( 0 ..^ ( # ` ( C ` q ) ) )
                (
                  ( C ` q ) ` j
                ) = if (
                  j < (
                    # ` (
                      A ` (
                        |_ ` ( q / ( # ` B ) )
                      )
                    )
                  ) ,
                  (
                    A ` (
                      |_ ` ( q / ( # ` B ) )
                    )
                  ) ` j ,
                  B ` ( q mod ( # ` B ) )
                )
            )
        )
      )
    )
  ) $.
$}

${
  $d k t A B $.

  verina26-expected-graph-definition $a |- (
    VERINA26ExpectedGraph A B
  ) <-> (
    (
      A e. Word VERINA26Char
      /\
      B e. Word ( Word VERINA26Char )
    )
    /\
    E. t e. Word ( Word ( Word VERINA26Char ) )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          (
            (
              # ` ( t ` 0 )
            ) = 1
            /\
            (
              ( t ` 0 ) ` 0
            ) = (/)
          )
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              VERINA26ExpectedStepGraph
                ( t ` k )
                ( VERINA26DigitToLetters ( A ` k ) )
                ( t ` ( k + 1 ) )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina26-expected-definition $a |- (
    VERINA26Expected A
  ) = (
    iota_ y e. Word ( Word VERINA26Char )
      ( VERINA26ExpectedGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina26-postcondition-definition $a |- (
    VERINA26Post A B
  ) <-> (
    (
      A e. Word VERINA26Char
      /\
      B e. Word ( Word VERINA26Char )
    )
    /\
    if (
      A = (/) ,
      B = (/) ,
      if (
        ( VERINA26HasInvalid A ) ,
        B = (/) ,
        (
          (
            # ` B
          ) = (
            # ` ( VERINA26Expected A )
          )
          /\
          (
            A. i e. ( 0 ..^ ( # ` B ) )
              (
                B ` i
              ) e. ran ( VERINA26Expected A )
            /\
            A. i e. (
              0 ..^ ( # ` ( VERINA26Expected A ) )
            )
              (
                ( VERINA26Expected A ) ` i
              ) e. ran B
          )
        )
      )
    )
  ) $.
$}

verina-advanced-26-letter-combinations
  $a |- A. w e. Word VERINA26Char
    (
      ( VERINA26Pre w )
      ->
      (
        VERINA26Post
          w
          ( VERINA26LetterCombinations w )
      )
    )
  $.
