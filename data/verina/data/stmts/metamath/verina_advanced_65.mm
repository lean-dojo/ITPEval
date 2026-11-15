$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_65 (verina__metamath__verina_advanced_65), catalog title
  reverseString: the exact accumulator-recursive program reverses an arbitrary
  Unicode string, together with its length and reversed-character-list
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA65Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINA65Char represents arbitrary Lean strings extensionally through
  String.toList. Word length is therefore String.length.

  VERINA65ToCharList and VERINA65StringMk are the source String.toList and
  String.mk conversions; both are extensionally the identity on this word
  representation. VERINA65ConsGraph and VERINA65Cons are exact character
  cons.

  VERINA65ReverseAuxGraph records the complete deterministic execution of the
  source-local reverseAux on arbitrary character-list and accumulator
  arguments. Its trace begins at the supplied accumulator and, for each input
  position from left to right, prepends that character to the current
  accumulator. The terminal trace entry is exactly the recursive helper's
  result. VERINA65ReverseAux selects this unique output, and
  VERINA65ReverseString composes the source toList, empty initial accumulator,
  helper, and String.mk operations. Its result is fixed independently of the
  postcondition.

  VERINA65ListReverseGraph and VERINA65ListReverse reproduce List.reverse
  exactly by length and zero-based indexed character equality. VERINA65Pre is
  the source True precondition on typed String inputs. VERINA65Post preserves
  both source conjuncts: result.length equals input.length, and result.toList
  equals input.toList.reverse. The proof-valued precondition argument is
  computationally and propositionally unused and is represented by the
  explicit antecedent of the final correctness assertion. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA65Char
  VERINA65ToCharList VERINA65StringMk
  VERINA65ConsGraph VERINA65Cons
  VERINA65ReverseAuxGraph VERINA65ReverseAux
  VERINA65ReverseString
  VERINA65ListReverseGraph VERINA65ListReverse
  VERINA65Pre VERINA65Post
$.

verina65-char-syntax
  $a class VERINA65Char $.
verina65-to-char-list-syntax
  $a class ( VERINA65ToCharList A ) $.
verina65-string-mk-syntax
  $a class ( VERINA65StringMk A ) $.
verina65-cons-graph-syntax
  $a wff ( VERINA65ConsGraph A B C ) $.
verina65-cons-syntax
  $a class ( VERINA65Cons A B ) $.
verina65-reverse-aux-graph-syntax
  $a wff ( VERINA65ReverseAuxGraph A B C ) $.
verina65-reverse-aux-syntax
  $a class ( VERINA65ReverseAux A B ) $.
verina65-program-syntax
  $a class ( VERINA65ReverseString A ) $.
verina65-list-reverse-graph-syntax
  $a wff ( VERINA65ListReverseGraph A B ) $.
verina65-list-reverse-syntax
  $a class ( VERINA65ListReverse A ) $.
verina65-precondition-syntax
  $a wff ( VERINA65Pre A ) $.
verina65-postcondition-syntax
  $a wff ( VERINA65Post A B ) $.

verina65-char-definition $a |- VERINA65Char =
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

verina65-to-char-list-definition $a |- (
  VERINA65ToCharList A
) = A $.

verina65-string-mk-definition $a |- (
  VERINA65StringMk A
) = A $.

${
  $d k A B C $.

  verina65-cons-graph-definition $a |- (
    VERINA65ConsGraph A B C
  ) <-> (
    (
      (
        A e. VERINA65Char
        /\
        B e. Word VERINA65Char
      )
      /\
      C e. Word VERINA65Char
    )
    /\
    (
      ( # ` C ) = ( ( # ` B ) + 1 )
      /\
      A. k e. ( 0 ..^ ( # ` C ) )
        (
          C ` k
        ) = if (
          k = 0 ,
          A ,
          ( B ` ( k - 1 ) )
        )
    )
  ) $.
$}

${
  $d y A B $.

  verina65-cons-definition $a |- (
    VERINA65Cons A B
  ) = (
    iota_ y e. Word VERINA65Char
      ( VERINA65ConsGraph A B y )
  ) $.
$}

${
  $d i t A B C $.

  verina65-reverse-aux-graph-definition $a |- (
    VERINA65ReverseAuxGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA65Char
        /\
        B e. Word VERINA65Char
      )
      /\
      C e. Word VERINA65Char
    )
    /\
    E. t e. Word ( Word VERINA65Char )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = B
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              t ` ( i + 1 )
            ) = (
              VERINA65Cons
                ( A ` i )
                ( t ` i )
            )
          /\
          C = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina65-reverse-aux-definition $a |- (
    VERINA65ReverseAux A B
  ) = (
    iota_ y e. Word VERINA65Char
      ( VERINA65ReverseAuxGraph A B y )
  ) $.
$}

verina65-program-definition $a |- (
  VERINA65ReverseString A
) = (
  VERINA65StringMk
    (
      VERINA65ReverseAux
        ( VERINA65ToCharList A )
        (/)
    )
) $.

${
  $d i A B $.

  verina65-list-reverse-graph-definition $a |- (
    VERINA65ListReverseGraph A B
  ) <-> (
    (
      A e. Word VERINA65Char
      /\
      B e. Word VERINA65Char
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

  verina65-list-reverse-definition $a |- (
    VERINA65ListReverse A
  ) = (
    iota_ y e. Word VERINA65Char
      ( VERINA65ListReverseGraph A y )
  ) $.
$}

verina65-precondition-definition $a |- (
  VERINA65Pre A
) <-> (
  A e. Word VERINA65Char
) $.

verina65-postcondition-definition $a |- (
  VERINA65Post A B
) <-> (
  (
    A e. Word VERINA65Char
    /\
    B e. Word VERINA65Char
  )
  /\
  (
    ( # ` B ) = ( # ` A )
    /\
    (
      VERINA65ToCharList B
    ) = (
      VERINA65ListReverse
        ( VERINA65ToCharList A )
    )
  )
) $.

verina-advanced-65-reverse-string $a |-
  A. w e. Word VERINA65Char
    (
      ( VERINA65Pre w )
      ->
      (
        VERINA65Post
          w
          ( VERINA65ReverseString w )
      )
    )
$.
