$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_31
  (verina__metamath__verina_basic_31), catalog title toUppercase: the exact
  executable character-map program converts ASCII lowercase characters in an
  arbitrary Unicode string by truncated subtraction of 32 modulo 128, leaves
  every other character unchanged, and satisfies its length and pointwise
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB31Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB31Char represents arbitrary Lean strings extensionally through
  String.toList. Word length is therefore String.length, word lookup is
  zero-based, and 0 ..^ ( # ` A ) is the complete valid-index set.

  VERINAB31IsLower is the source Boolean helper for the inclusive ASCII range
  a through z. VERINAB31NatSub is Lean's truncated natural subtraction.
  VERINAB31ShiftMinus32 exactly represents
  Char.ofNat ((c.toNat - 32) % 128): it computes the truncated difference and
  remainder, then returns that code point when it is a Unicode scalar value
  and Lean's null character otherwise. The remainder is always an ASCII
  scalar for every source Char input.

  VERINAB31ToCharList and VERINAB31StringMk are the source String.toList and
  String.mk conversions; both are extensionally the identity on this word
  representation. VERINAB31MapGraph is exactly List.map with the source
  branch fun c => if isLowerCase c then shiftMinus32 c else c: it preserves
  length and fixes every output position to that branch value.
  VERINAB31Map selects the unique mapped word, and VERINAB31ToUppercase
  composes the source conversions and map. Its result is fixed independently
  of the postcondition and admits no additional outputs.

  VERINAB31Pre is the source True precondition on typed String inputs.
  VERINAB31Post preserves result.length = s.length and both source
  implications at every valid input index. Because those lengths are equal,
  direct word lookup there is exactly the source get! lookup on both lists.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB31Char
  VERINAB31IsLower VERINAB31NatSub VERINAB31ShiftMinus32
  VERINAB31ToCharList VERINAB31StringMk
  VERINAB31MapGraph VERINAB31Map
  VERINAB31Pre VERINAB31ToUppercase VERINAB31Post
$.

verinab31-char-syntax
  $a class VERINAB31Char $.
verinab31-is-lower-syntax
  $a class ( VERINAB31IsLower A ) $.
verinab31-nat-sub-syntax
  $a class ( VERINAB31NatSub A B ) $.
verinab31-shift-minus32-syntax
  $a class ( VERINAB31ShiftMinus32 A ) $.
verinab31-to-char-list-syntax
  $a class ( VERINAB31ToCharList A ) $.
verinab31-string-mk-syntax
  $a class ( VERINAB31StringMk A ) $.
verinab31-map-graph-syntax
  $a wff ( VERINAB31MapGraph A B ) $.
verinab31-map-syntax
  $a class ( VERINAB31Map A ) $.
verinab31-precondition-syntax
  $a wff ( VERINAB31Pre A ) $.
verinab31-program-syntax
  $a class ( VERINAB31ToUppercase A ) $.
verinab31-postcondition-syntax
  $a wff ( VERINAB31Post A B ) $.

verinab31-char-definition $a |- VERINAB31Char =
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

verinab31-is-lower-definition $a |- (
  VERINAB31IsLower A
) = if (
  (
    ; 9 7 <_ A
    /\
    A <_ ; ; 1 2 2
  ) ,
  1 ,
  0
) $.

verinab31-nat-sub-definition $a |- (
  VERINAB31NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab31-shift-minus32-definition $a |- (
  VERINAB31ShiftMinus32 A
) = if (
  (
    ( VERINAB31NatSub A ( ; 3 2 ) )
    mod
    ; ; 1 2 8
  ) e. VERINAB31Char ,
  (
    ( VERINAB31NatSub A ( ; 3 2 ) )
    mod
    ; ; 1 2 8
  ) ,
  0
) $.

verinab31-to-char-list-definition $a |- (
  VERINAB31ToCharList A
) = A $.

verinab31-string-mk-definition $a |- (
  VERINAB31StringMk A
) = A $.

${
  $d k A B $.

  verinab31-map-graph-definition $a |- (
    VERINAB31MapGraph A B
  ) <-> (
    (
      A e. Word VERINAB31Char
      /\
      B e. Word VERINAB31Char
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        (
          B ` k
        ) = if (
          ( VERINAB31IsLower ( A ` k ) ) = 1 ,
          ( VERINAB31ShiftMinus32 ( A ` k ) ) ,
          A ` k
        )
    )
  ) $.
$}

${
  $d y A $.

  verinab31-map-definition $a |- (
    VERINAB31Map A
  ) = (
    iota_ y e. Word VERINAB31Char
      ( VERINAB31MapGraph A y )
  ) $.
$}

verinab31-precondition-definition $a |- (
  VERINAB31Pre A
) <-> (
  A e. Word VERINAB31Char
) $.

verinab31-program-definition $a |- (
  VERINAB31ToUppercase A
) = (
  VERINAB31StringMk
    (
      VERINAB31Map
        ( VERINAB31ToCharList A )
    )
) $.

${
  $d i A B $.

  verinab31-postcondition-definition $a |- (
    VERINAB31Post A B
  ) <-> (
    (
      A e. Word VERINAB31Char
      /\
      B e. Word VERINAB31Char
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. (
        0 ..^ ( # ` ( VERINAB31ToCharList A ) )
      )
        (
          (
            (
              VERINAB31IsLower
                ( ( VERINAB31ToCharList A ) ` i )
            ) = 1
            ->
            (
              ( VERINAB31ToCharList B ) ` i
            ) = (
              VERINAB31ShiftMinus32
                ( ( VERINAB31ToCharList A ) ` i )
            )
          )
          /\
          (
            (
              VERINAB31IsLower
                ( ( VERINAB31ToCharList A ) ` i )
            ) = 0
            ->
            (
              ( VERINAB31ToCharList B ) ` i
            ) = (
              ( VERINAB31ToCharList A ) ` i
            )
          )
        )
    )
  ) $.
$}

verina-basic-31-to-uppercase $a |-
  A. s e. Word VERINAB31Char
    (
      ( VERINAB31Pre s )
      ->
      (
        VERINAB31Post
          s
          ( VERINAB31ToUppercase s )
      )
    )
$.
