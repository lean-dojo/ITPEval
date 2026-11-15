$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_38
  (verina__metamath__verina_basic_38), catalog title allCharactersSame: the
  exact executable Boolean scan of an arbitrary Unicode string returns true
  exactly when every character equals the first, including for empty and
  singleton strings, and satisfies its complete correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB38Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB38Char represents arbitrary Lean strings extensionally through
  String.toList. For a word w, # ` w is its natural-number length, w ` i is
  zero-based lookup, and 0 ..^ ( # ` w ) is its complete valid-index set.
  The Boolean domain is represented by { 0 , 1 }, with false = 0 and true = 1.

  VERINAB38ToCharList is the source String.toList conversion and is
  extensionally the identity on this representation. VERINAB38AllTailEqual
  is exactly cs.all (fun x => x = c) in the source nonempty branch: every
  position after zero equals the character at zero. VERINAB38AllCharactersSame
  returns one on the empty word and otherwise returns the exact Boolean value
  of that tail scan. Thus the executable result is fixed independently of the
  postcondition and admits no additional outputs.

  VERINAB38PairwiseEqual is exactly List.Pairwise equality, expressed over
  every earlier/later valid-index pair. VERINAB38GetBangZero is source get!
  at index zero, including the inhabited Unicode NUL default for the empty
  list. VERINAB38AnyDifferent is exactly the source List.any inequality scan
  against that value.

  VERINAB38Pre is the source True precondition on typed String inputs.
  VERINAB38Post preserves both source implications: a true result implies
  pairwise equality, while a false result implies a nonempty character list
  with some character different from get! zero. The proof-valued precondition
  argument is computationally and propositionally unused and is represented
  by the explicit antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB38Char VERINAB38ToCharList
  VERINAB38AllTailEqual VERINAB38Pre VERINAB38AllCharactersSame
  VERINAB38PairwiseEqual VERINAB38GetBangZero VERINAB38AnyDifferent
  VERINAB38Post
$.

verinab38-char-syntax
  $a class VERINAB38Char $.
verinab38-to-char-list-syntax
  $a class ( VERINAB38ToCharList A ) $.
verinab38-all-tail-equal-syntax
  $a wff ( VERINAB38AllTailEqual A ) $.
verinab38-precondition-syntax
  $a wff ( VERINAB38Pre A ) $.
verinab38-program-syntax
  $a class ( VERINAB38AllCharactersSame A ) $.
verinab38-pairwise-equal-syntax
  $a wff ( VERINAB38PairwiseEqual A ) $.
verinab38-get-bang-zero-syntax
  $a class ( VERINAB38GetBangZero A ) $.
verinab38-any-different-syntax
  $a wff ( VERINAB38AnyDifferent A ) $.
verinab38-postcondition-syntax
  $a wff ( VERINAB38Post A B ) $.

verinab38-char-definition $a |- VERINAB38Char =
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

verinab38-to-char-list-definition $a |- (
  VERINAB38ToCharList A
) = A $.

${
  $d i A $.

  verinab38-all-tail-equal-definition $a |- (
    VERINAB38AllTailEqual A
  ) <-> (
    A e. Word VERINAB38Char
    /\
    A. i e. ( 1 ..^ ( # ` A ) )
      ( A ` i ) = ( A ` 0 )
  ) $.
$}

verinab38-precondition-definition $a |- (
  VERINAB38Pre A
) <-> (
  A e. Word VERINAB38Char
) $.

verinab38-program-definition $a |- (
  VERINAB38AllCharactersSame A
) = if (
  A = (/) ,
  1 ,
  if (
    ( VERINAB38AllTailEqual ( VERINAB38ToCharList A ) ) ,
    1 ,
    0
  )
) $.

${
  $d i j A $.

  verinab38-pairwise-equal-definition $a |- (
    VERINAB38PairwiseEqual A
  ) <-> (
    A e. Word VERINAB38Char
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) = ( A ` j )
        )
  ) $.
$}

verinab38-get-bang-zero-definition $a |- (
  VERINAB38GetBangZero A
) = if (
  A = (/) ,
  0 ,
  ( A ` 0 )
) $.

${
  $d i A $.

  verinab38-any-different-definition $a |- (
    VERINAB38AnyDifferent A
  ) <-> (
    A e. Word VERINAB38Char
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      ( A ` i ) =/= ( VERINAB38GetBangZero A )
  ) $.
$}

verinab38-postcondition-definition $a |- (
  VERINAB38Post A B
) <-> (
  (
    A e. Word VERINAB38Char
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    (
      B = 1
      ->
      (
        VERINAB38PairwiseEqual
          ( VERINAB38ToCharList A )
      )
    )
    /\
    (
      B = 0
      ->
      (
        ( VERINAB38ToCharList A ) =/= (/)
        /\
        (
          VERINAB38AnyDifferent
            ( VERINAB38ToCharList A )
        )
      )
    )
  )
) $.

verina-basic-38-all-characters-same $a |-
  A. s e. Word VERINAB38Char
    (
      ( VERINAB38Pre s )
      ->
      (
        VERINAB38Post
          s
          ( VERINAB38AllCharactersSame s )
      )
    )
$.
