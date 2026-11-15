$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_36
  (verina__metamath__verina_basic_36), catalog title replaceWithColon: the
  exact executable character-map program replaces every space, comma, or dot
  in an arbitrary Unicode string with a colon, leaves every other character
  unchanged, and satisfies its length and pointwise replacement correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB36Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB36Char represents arbitrary Lean strings extensionally through
  String.toList. Word length is therefore String.length, word lookup is
  zero-based, and 0 ..^ ( # ` A ) is the complete valid-index set.

  VERINAB36IsSpaceCommaDot is the source Boolean helper isSpaceCommaDot: it is
  one exactly for the Unicode scalar values of ASCII space (32), comma (44),
  and dot (46), and zero for every other character.

  VERINAB36ToCharList and VERINAB36StringMk are the source String.toList and
  String.mk conversions; both are extensionally the identity on this word
  representation. VERINAB36MapGraph is exactly List.map with the source branch
  fun c => if isSpaceCommaDot c then ':' else c: it preserves length and fixes
  every output position to that branch value. VERINAB36Map selects the unique
  mapped word, and VERINAB36ReplaceWithColon composes the source conversions
  and map. Its result is fixed independently of the postcondition and admits
  no additional outputs.

  VERINAB36Pre is the source True precondition on typed String inputs.
  VERINAB36Post preserves result.length = s.length and both source
  implications at every valid input index. Because those lengths are equal,
  direct word lookup there is exactly the source get! lookup on both lists.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB36Char VERINAB36IsSpaceCommaDot
  VERINAB36ToCharList VERINAB36StringMk
  VERINAB36MapGraph VERINAB36Map
  VERINAB36Pre VERINAB36ReplaceWithColon VERINAB36Post
$.

verinab36-char-syntax
  $a class VERINAB36Char $.
verinab36-is-space-comma-dot-syntax
  $a class ( VERINAB36IsSpaceCommaDot A ) $.
verinab36-to-char-list-syntax
  $a class ( VERINAB36ToCharList A ) $.
verinab36-string-mk-syntax
  $a class ( VERINAB36StringMk A ) $.
verinab36-map-graph-syntax
  $a wff ( VERINAB36MapGraph A B ) $.
verinab36-map-syntax
  $a class ( VERINAB36Map A ) $.
verinab36-precondition-syntax
  $a wff ( VERINAB36Pre A ) $.
verinab36-program-syntax
  $a class ( VERINAB36ReplaceWithColon A ) $.
verinab36-postcondition-syntax
  $a wff ( VERINAB36Post A B ) $.

verinab36-char-definition $a |- VERINAB36Char =
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

verinab36-is-space-comma-dot-definition $a |- (
  VERINAB36IsSpaceCommaDot A
) = if (
  (
    (
      A = ( ; 3 2 )
      \/
      A = ( ; 4 4 )
    )
    \/
    A = ( ; 4 6 )
  ) ,
  1 ,
  0
) $.

verinab36-to-char-list-definition $a |- (
  VERINAB36ToCharList A
) = A $.

verinab36-string-mk-definition $a |- (
  VERINAB36StringMk A
) = A $.

${
  $d k A B $.

  verinab36-map-graph-definition $a |- (
    VERINAB36MapGraph A B
  ) <-> (
    (
      A e. Word VERINAB36Char
      /\
      B e. Word VERINAB36Char
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        (
          B ` k
        ) = if (
          ( VERINAB36IsSpaceCommaDot ( A ` k ) ) = 1 ,
          ( ; 5 8 ) ,
          A ` k
        )
    )
  ) $.
$}

${
  $d y A $.

  verinab36-map-definition $a |- (
    VERINAB36Map A
  ) = (
    iota_ y e. Word VERINAB36Char
      ( VERINAB36MapGraph A y )
  ) $.
$}

verinab36-precondition-definition $a |- (
  VERINAB36Pre A
) <-> (
  A e. Word VERINAB36Char
) $.

verinab36-program-definition $a |- (
  VERINAB36ReplaceWithColon A
) = (
  VERINAB36StringMk
    (
      VERINAB36Map
        ( VERINAB36ToCharList A )
    )
) $.

${
  $d i A B $.

  verinab36-postcondition-definition $a |- (
    VERINAB36Post A B
  ) <-> (
    (
      A e. Word VERINAB36Char
      /\
      B e. Word VERINAB36Char
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. (
        0 ..^ ( # ` ( VERINAB36ToCharList A ) )
      )
        (
          (
            (
              VERINAB36IsSpaceCommaDot
                ( ( VERINAB36ToCharList A ) ` i )
            ) = 1
            ->
            (
              ( VERINAB36ToCharList B ) ` i
            ) = ( ; 5 8 )
          )
          /\
          (
            (
              VERINAB36IsSpaceCommaDot
                ( ( VERINAB36ToCharList A ) ` i )
            ) = 0
            ->
            (
              ( VERINAB36ToCharList B ) ` i
            ) = (
              ( VERINAB36ToCharList A ) ` i
            )
          )
        )
    )
  ) $.
$}

verina-basic-36-replace-with-colon $a |-
  A. s e. Word VERINAB36Char
    (
      ( VERINAB36Pre s )
      ->
      (
        VERINAB36Post
          s
          ( VERINAB36ReplaceWithColon s )
      )
    )
$.
