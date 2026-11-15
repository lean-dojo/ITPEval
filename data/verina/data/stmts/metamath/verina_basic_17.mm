$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_17
  (verina__metamath__verina_basic_17), catalog title toLowercase: the exact
  executable character-map program converts ASCII uppercase characters in an
  arbitrary Unicode string by adding 32 to their code points, leaves every
  other character unchanged, and satisfies its length and pointwise
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB17Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB17Char represents arbitrary Lean strings extensionally through
  String.toList. Word length is therefore String.length, word lookup is
  zero-based, and 0 ..^ ( # ` A ) is the complete valid-index set.

  VERINAB17IsUpper is the source Boolean helper for the inclusive ASCII range
  A through Z. VERINAB17Shift32 exactly represents Char.ofNat
  (c.toNat + 32): it returns the sum when that sum is a Unicode scalar value
  and Lean's null character otherwise. In every executable uppercase branch
  the sum is a valid lowercase ASCII scalar.

  VERINAB17ToCharList and VERINAB17StringMk are the source String.toList and
  String.mk conversions; both are extensionally the identity on this word
  representation. VERINAB17MapGraph is exactly List.map with the source
  branch fun c => if isUpperCase c then shift32 c else c: it preserves length
  and fixes every output position to that branch value. VERINAB17Map selects
  the unique mapped word, and VERINAB17ToLowercase composes the source
  conversions and map. Its result is fixed independently of the postcondition
  and admits no additional outputs.

  VERINAB17Pre is the source True precondition on typed String inputs.
  VERINAB17Post preserves result.length = s.length and both source
  implications at every valid input index. Because those lengths are equal,
  direct word lookup there is exactly the source get! lookup on both lists.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB17Char
  VERINAB17IsUpper VERINAB17Shift32
  VERINAB17ToCharList VERINAB17StringMk
  VERINAB17MapGraph VERINAB17Map
  VERINAB17Pre VERINAB17ToLowercase VERINAB17Post
$.

verinab17-char-syntax
  $a class VERINAB17Char $.
verinab17-is-upper-syntax
  $a class ( VERINAB17IsUpper A ) $.
verinab17-shift32-syntax
  $a class ( VERINAB17Shift32 A ) $.
verinab17-to-char-list-syntax
  $a class ( VERINAB17ToCharList A ) $.
verinab17-string-mk-syntax
  $a class ( VERINAB17StringMk A ) $.
verinab17-map-graph-syntax
  $a wff ( VERINAB17MapGraph A B ) $.
verinab17-map-syntax
  $a class ( VERINAB17Map A ) $.
verinab17-precondition-syntax
  $a wff ( VERINAB17Pre A ) $.
verinab17-program-syntax
  $a class ( VERINAB17ToLowercase A ) $.
verinab17-postcondition-syntax
  $a wff ( VERINAB17Post A B ) $.

verinab17-char-definition $a |- VERINAB17Char =
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

verinab17-is-upper-definition $a |- (
  VERINAB17IsUpper A
) = if (
  (
    ; 6 5 <_ A
    /\
    A <_ ; 9 0
  ) ,
  1 ,
  0
) $.

verinab17-shift32-definition $a |- (
  VERINAB17Shift32 A
) = if (
  ( A + ; 3 2 ) e. VERINAB17Char ,
  ( A + ; 3 2 ) ,
  0
) $.

verinab17-to-char-list-definition $a |- (
  VERINAB17ToCharList A
) = A $.

verinab17-string-mk-definition $a |- (
  VERINAB17StringMk A
) = A $.

${
  $d k A B $.

  verinab17-map-graph-definition $a |- (
    VERINAB17MapGraph A B
  ) <-> (
    (
      A e. Word VERINAB17Char
      /\
      B e. Word VERINAB17Char
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        (
          B ` k
        ) = if (
          ( VERINAB17IsUpper ( A ` k ) ) = 1 ,
          ( VERINAB17Shift32 ( A ` k ) ) ,
          A ` k
        )
    )
  ) $.
$}

${
  $d y A $.

  verinab17-map-definition $a |- (
    VERINAB17Map A
  ) = (
    iota_ y e. Word VERINAB17Char
      ( VERINAB17MapGraph A y )
  ) $.
$}

verinab17-precondition-definition $a |- (
  VERINAB17Pre A
) <-> (
  A e. Word VERINAB17Char
) $.

verinab17-program-definition $a |- (
  VERINAB17ToLowercase A
) = (
  VERINAB17StringMk
    (
      VERINAB17Map
        ( VERINAB17ToCharList A )
    )
) $.

${
  $d i A B $.

  verinab17-postcondition-definition $a |- (
    VERINAB17Post A B
  ) <-> (
    (
      A e. Word VERINAB17Char
      /\
      B e. Word VERINAB17Char
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. (
        0 ..^ ( # ` ( VERINAB17ToCharList A ) )
      )
        (
          (
            (
              VERINAB17IsUpper
                ( ( VERINAB17ToCharList A ) ` i )
            ) = 1
            ->
            (
              ( VERINAB17ToCharList B ) ` i
            ) = (
              VERINAB17Shift32
                ( ( VERINAB17ToCharList A ) ` i )
            )
          )
          /\
          (
            (
              VERINAB17IsUpper
                ( ( VERINAB17ToCharList A ) ` i )
            ) = 0
            ->
            (
              ( VERINAB17ToCharList B ) ` i
            ) = (
              ( VERINAB17ToCharList A ) ` i
            )
          )
        )
    )
  ) $.
$}

verina-basic-17-to-lowercase $a |-
  A. s e. Word VERINAB17Char
    (
      ( VERINAB17Pre s )
      ->
      (
        VERINAB17Post
          s
          ( VERINAB17ToLowercase s )
      )
    )
$.
