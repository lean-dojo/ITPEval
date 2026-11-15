$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_73
  (verina__metamath__verina_basic_73), catalog title Match: the exact
  executable left-to-right Unicode-string scan decides whether equal-length
  strings agree at every position or the pattern has a question-mark
  wildcard there, together with its Boolean correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB73Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB73Char represents arbitrary Lean strings extensionally through
  String.toList. For a word w, # ` w is its natural-number character length,
  w ` i is zero-based lookup, and 0 ..^ ( # ` w ) is its complete valid
  character-index set. The Boolean domain is { 0 , 1 }, with false = 0 and
  true = 1. VERINAB73Question is the Unicode code point 63 for '?'.

  VERINAB73ToCharList is String.toList and is extensionally the identity on
  this finite character-word representation. VERINAB73GetBang reproduces
  Lean List.get! on character lists, including its inhabited NUL default
  outside the valid index range.

  VERINAB73LoopGraph records the Boolean result of the source local loop at
  every character position. The terminal position has value true. At each
  earlier position, unequal characters with a non-question-mark pattern
  character give false; otherwise the value is exactly the next position's
  value. An initial index beyond the end also gives true, as in the source
  guard. This complete suffix table is an exact graph of the recursion and
  admits no additional output. VERINAB73Loop selects its unique result, and
  VERINAB73Match invokes it at index zero.

  VERINAB73Pre is the source precondition requiring equal String.toList
  lengths. VERINAB73Post preserves the source equivalence between a true
  result and every natural index below the source-string length having equal
  characters or a question-mark pattern character. The proof-valued
  precondition arguments are computationally erased and are represented by
  the explicit precondition antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB73Char VERINAB73Question
  VERINAB73ToCharList VERINAB73GetBang
  VERINAB73LoopGraph VERINAB73Loop
  VERINAB73Pre VERINAB73Match VERINAB73Post
$.

verinab73-char-syntax
  $a class VERINAB73Char $.
verinab73-question-syntax
  $a class VERINAB73Question $.
verinab73-to-char-list-syntax
  $a class ( VERINAB73ToCharList A ) $.
verinab73-get-bang-syntax
  $a class ( VERINAB73GetBang A B ) $.
verinab73-loop-graph-syntax
  $a wff ( VERINAB73LoopGraph A B C D ) $.
verinab73-loop-syntax
  $a class ( VERINAB73Loop A B C ) $.
verinab73-precondition-syntax
  $a wff ( VERINAB73Pre A B ) $.
verinab73-program-syntax
  $a class ( VERINAB73Match A B ) $.
verinab73-postcondition-syntax
  $a wff ( VERINAB73Post A B C ) $.

verinab73-char-definition $a |- VERINAB73Char =
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

verinab73-question-definition $a |- VERINAB73Question = ; 6 3 $.

verinab73-to-char-list-definition $a |- (
  VERINAB73ToCharList A
) = A $.

verinab73-get-bang-definition $a |- (
  VERINAB73GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k t A B C D $.

  verinab73-loop-graph-definition $a |- (
    VERINAB73LoopGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word VERINAB73Char
          /\
          B e. Word VERINAB73Char
        )
        /\
        C e. NN0
      )
      /\
      D e. { 0 , 1 }
    )
    /\
    E. t e. Word { 0 , 1 }
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` ( # ` A ) ) = 1
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              t ` k
            ) = if (
              (
                (
                  VERINAB73GetBang A k
                ) =/= (
                  VERINAB73GetBang B k
                )
                /\
                (
                  VERINAB73GetBang B k
                ) =/= VERINAB73Question
              ) ,
              0 ,
              ( t ` ( k + 1 ) )
            )
          /\
          D = if (
            C < ( # ` A ) ,
            ( t ` C ) ,
            1
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab73-loop-definition $a |- (
    VERINAB73Loop A B C
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINAB73LoopGraph A B C y )
  ) $.
$}

verinab73-precondition-definition $a |- (
  VERINAB73Pre A B
) <-> (
  (
    A e. Word VERINAB73Char
    /\
    B e. Word VERINAB73Char
  )
  /\
  (
    # ` ( VERINAB73ToCharList A )
  ) = (
    # ` ( VERINAB73ToCharList B )
  )
) $.

verinab73-program-definition $a |- (
  VERINAB73Match A B
) = (
  VERINAB73Loop A B 0
) $.

${
  $d n A B C $.

  verinab73-postcondition-definition $a |- (
    VERINAB73Post A B C
  ) <-> (
    (
      (
        A e. Word VERINAB73Char
        /\
        B e. Word VERINAB73Char
      )
      /\
      C e. { 0 , 1 }
    )
    /\
    (
      C = 1
      <->
      A. n e. NN0
        (
          n < (
            # ` ( VERINAB73ToCharList A )
          )
          ->
          (
            (
              VERINAB73GetBang
                ( VERINAB73ToCharList A )
                n
            ) = (
              VERINAB73GetBang
                ( VERINAB73ToCharList B )
                n
            )
            \/
            (
              VERINAB73GetBang
                ( VERINAB73ToCharList B )
                n
            ) = VERINAB73Question
          )
        )
    )
  ) $.
$}

verina-basic-73-match $a |-
  A. s e. Word VERINAB73Char
    A. p e. Word VERINAB73Char
      (
        ( VERINAB73Pre s p )
        ->
        (
          VERINAB73Post
            s
            p
            ( VERINAB73Match s p )
        )
      )
$.
