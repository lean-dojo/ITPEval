$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_6 (verina__metamath__verina_advanced_6), catalog title
  allVowels: the exact case-insensitive program lowercases ASCII uppercase
  characters in an arbitrary Unicode string and returns true exactly when
  the normalized string contains all five English vowels, together with its
  complete correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA6Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINA6Char represents arbitrary Lean strings extensionally through
  String.data. VERINA6IsUpper and VERINA6ToLower reproduce the source helper:
  only basic-Latin A through Z are changed, by adding 32, while every other
  Unicode scalar value is unchanged.

  VERINA6NormalizeGraph maps that helper pointwise over the complete input
  word, and VERINA6Normalize selects its unique output; this is exactly
  normalize_str. VERINA6Contains is List.contains for a character, expressed
  by occurrence at an input index. VERINA6HasAllVowels is the exact Boolean
  conjunction produced by List.all on the source list
  ['a', 'e', 'i', 'o', 'u'], using code points 97, 101, 105, 111, and 117.

  VERINA6AllVowels returns one precisely when that conjunction holds for the
  normalized input and zero otherwise, so its result is fixed by the source
  computation independently of the postcondition. VERINA6Pre is the source
  True precondition on typed string inputs. VERINA6Post states the source
  Boolean equivalence between the result and the same five-vowel test. The
  proof-valued precondition argument is computationally and propositionally
  unused and is represented by the explicit antecedent of the final
  correctness assertion. Every earlier $a is syntax or a faithful definition,
  and this database has no $p declaration.
$)

$c
  VERINA6Char
  VERINA6IsUpper VERINA6ToLower
  VERINA6NormalizeGraph VERINA6Normalize
  VERINA6Contains VERINA6HasAllVowels
  VERINA6Pre VERINA6AllVowels VERINA6Post
$.

verina6-char-syntax
  $a class VERINA6Char $.
verina6-is-upper-syntax
  $a class ( VERINA6IsUpper A ) $.
verina6-to-lower-syntax
  $a class ( VERINA6ToLower A ) $.
verina6-normalize-graph-syntax
  $a wff ( VERINA6NormalizeGraph A B ) $.
verina6-normalize-syntax
  $a class ( VERINA6Normalize A ) $.
verina6-contains-syntax
  $a wff ( VERINA6Contains A B ) $.
verina6-has-all-vowels-syntax
  $a wff ( VERINA6HasAllVowels A ) $.
verina6-precondition-syntax
  $a wff ( VERINA6Pre A ) $.
verina6-program-syntax
  $a class ( VERINA6AllVowels A ) $.
verina6-postcondition-syntax
  $a wff ( VERINA6Post A B ) $.

verina6-char-definition $a |- VERINA6Char =
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

verina6-is-upper-definition $a |- (
  VERINA6IsUpper A
) = if (
  (
    ; 6 5 <_ A
    /\
    A <_ ; 9 0
  ) ,
  1 ,
  0
) $.

verina6-to-lower-definition $a |- (
  VERINA6ToLower A
) = if (
  ( VERINA6IsUpper A ) = 1 ,
  ( A + ; 3 2 ) ,
  A
) $.

${
  $d i A B $.

  verina6-normalize-graph-definition $a |- (
    VERINA6NormalizeGraph A B
  ) <-> (
    (
      A e. Word VERINA6Char
      /\
      B e. Word VERINA6Char
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( B ` i ) = ( VERINA6ToLower ( A ` i ) )
    )
  ) $.
$}

${
  $d y A $.

  verina6-normalize-definition $a |- (
    VERINA6Normalize A
  ) = (
    iota_ y e. Word VERINA6Char
      ( VERINA6NormalizeGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina6-contains-definition $a |- (
    VERINA6Contains A B
  ) <-> (
    (
      A e. Word VERINA6Char
      /\
      B e. VERINA6Char
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      ( A ` i ) = B
  ) $.
$}

verina6-has-all-vowels-definition $a |- (
  VERINA6HasAllVowels A
) <-> (
  A e. Word VERINA6Char
  /\
  (
    ( VERINA6Contains A ; 9 7 )
    /\
    (
      ( VERINA6Contains A ; ; 1 0 1 )
      /\
      (
        ( VERINA6Contains A ; ; 1 0 5 )
        /\
        (
          ( VERINA6Contains A ; ; 1 1 1 )
          /\
          ( VERINA6Contains A ; ; 1 1 7 )
        )
      )
    )
  )
) $.

verina6-precondition-definition $a |- (
  VERINA6Pre A
) <-> (
  A e. Word VERINA6Char
) $.

verina6-program-definition $a |- (
  VERINA6AllVowels A
) = if (
  ( VERINA6HasAllVowels ( VERINA6Normalize A ) ) ,
  1 ,
  0
) $.

verina6-postcondition-definition $a |- (
  VERINA6Post A B
) <-> (
  (
    A e. Word VERINA6Char
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    B = 1
    <->
    ( VERINA6HasAllVowels ( VERINA6Normalize A ) )
  )
) $.

verina-advanced-6-all-vowels $a |- A. w e. Word VERINA6Char
  (
    ( VERINA6Pre w )
    ->
    (
      VERINA6Post
        w
        ( VERINA6AllVowels w )
    )
  )
$.
