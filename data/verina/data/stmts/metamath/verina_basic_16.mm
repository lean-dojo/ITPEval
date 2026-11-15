$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_16
  (verina__metamath__verina_basic_16), catalog title replaceChars: the exact
  executable character-map program replaces every occurrence of one character
  in an arbitrary Unicode string with another character and satisfies its
  length and pointwise replacement correctness contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB16Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB16Char represents arbitrary Lean strings extensionally through
  String.toList. Word length is therefore String.length, word lookup is
  zero-based, and 0 ..^ ( # ` A ) is the complete valid-index set.

  VERINAB16ToCharList and VERINAB16StringMk are the source String.toList and
  String.mk conversions; both are extensionally the identity on this word
  representation. VERINAB16MapGraph is exactly List.map with the source
  branch fun c => if c = oldChar then newChar else c: it preserves length and
  fixes every output position to that branch value. VERINAB16Map selects the
  unique mapped word, and VERINAB16ReplaceChars composes the source
  conversions and map. Its result is fixed independently of the postcondition
  and admits no additional outputs.

  VERINAB16Pre is the source True precondition on typed String and Char
  inputs. VERINAB16Post preserves result.length = s.length and both source
  implications at every valid input index. Because those lengths are equal,
  direct word lookup there is exactly the source get! lookup on both lists.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB16Char
  VERINAB16ToCharList VERINAB16StringMk
  VERINAB16MapGraph VERINAB16Map
  VERINAB16Pre VERINAB16ReplaceChars VERINAB16Post
$.

verinab16-char-syntax
  $a class VERINAB16Char $.
verinab16-to-char-list-syntax
  $a class ( VERINAB16ToCharList A ) $.
verinab16-string-mk-syntax
  $a class ( VERINAB16StringMk A ) $.
verinab16-map-graph-syntax
  $a wff ( VERINAB16MapGraph A B C D ) $.
verinab16-map-syntax
  $a class ( VERINAB16Map A B C ) $.
verinab16-precondition-syntax
  $a wff ( VERINAB16Pre A B C ) $.
verinab16-program-syntax
  $a class ( VERINAB16ReplaceChars A B C ) $.
verinab16-postcondition-syntax
  $a wff ( VERINAB16Post A B C D ) $.

verinab16-char-definition $a |- VERINAB16Char =
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

verinab16-to-char-list-definition $a |- (
  VERINAB16ToCharList A
) = A $.

verinab16-string-mk-definition $a |- (
  VERINAB16StringMk A
) = A $.

${
  $d k A B C D $.

  verinab16-map-graph-definition $a |- (
    VERINAB16MapGraph A B C D
  ) <-> (
    (
      (
        A e. Word VERINAB16Char
        /\
        B e. VERINAB16Char
      )
      /\
      (
        C e. VERINAB16Char
        /\
        D e. Word VERINAB16Char
      )
    )
    /\
    (
      ( # ` D ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        (
          D ` k
        ) = if (
          ( A ` k ) = B ,
          C ,
          A ` k
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab16-map-definition $a |- (
    VERINAB16Map A B C
  ) = (
    iota_ y e. Word VERINAB16Char
      ( VERINAB16MapGraph A B C y )
  ) $.
$}

verinab16-precondition-definition $a |- (
  VERINAB16Pre A B C
) <-> (
  (
    A e. Word VERINAB16Char
    /\
    B e. VERINAB16Char
  )
  /\
  C e. VERINAB16Char
) $.

verinab16-program-definition $a |- (
  VERINAB16ReplaceChars A B C
) = (
  VERINAB16StringMk
    (
      VERINAB16Map
        ( VERINAB16ToCharList A )
        B
        C
    )
) $.

${
  $d i A B C D $.

  verinab16-postcondition-definition $a |- (
    VERINAB16Post A B C D
  ) <-> (
    (
      (
        (
          A e. Word VERINAB16Char
          /\
          B e. VERINAB16Char
        )
        /\
        C e. VERINAB16Char
      )
      /\
      D e. Word VERINAB16Char
    )
    /\
    (
      ( # ` D ) = ( # ` A )
      /\
      A. i e. (
        0 ..^ ( # ` ( VERINAB16ToCharList A ) )
      )
        (
          (
            (
              ( VERINAB16ToCharList A ) ` i
            ) = B
            ->
            (
              ( VERINAB16ToCharList D ) ` i
            ) = C
          )
          /\
          (
            (
              ( VERINAB16ToCharList A ) ` i
            ) =/= B
            ->
            (
              ( VERINAB16ToCharList D ) ` i
            ) = (
              ( VERINAB16ToCharList A ) ` i
            )
          )
        )
    )
  ) $.
$}

verina-basic-16-replace-chars $a |-
  A. s e. Word VERINAB16Char
    A. o e. VERINAB16Char
      A. n e. VERINAB16Char
        (
          ( VERINAB16Pre s o n )
          ->
          (
            VERINAB16Post
              s
              o
              n
              ( VERINAB16ReplaceChars s o n )
          )
        )
$.
