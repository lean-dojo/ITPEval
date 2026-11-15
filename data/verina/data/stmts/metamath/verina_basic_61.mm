$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_61
  (verina__metamath__verina_basic_61), catalog title allDigits: the exact
  executable Unicode-string iterator returns true precisely when every
  character is an ASCII digit from '0' through '9', including true on the
  empty string, together with its unconditional correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB61Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB61Char represents arbitrary Lean strings extensionally through
  String.toList. For a word w, # ` w is its character length, w ` i is
  zero-based character lookup, and 0 ..^ ( # ` w ) is its complete valid
  character-index set. The Boolean domain is { 0 , 1 }, with false = 0 and
  true = 1.

  VERINAB61IsDigit is the source Boolean helper: it returns one exactly for
  character codes 48 through 57, the inclusive ASCII range '0' through '9'.
  VERINAB61ToCharList is String.toList and is extensionally the identity on
  this finite character-word representation.

  VERINAB61LoopGraph records the result of the source local loop at every
  valid iterator position. The at-end position has value one. At each earlier
  position, a non-digit current character has value zero, while a digit takes
  exactly the value at the next character position. This is the same
  atEnd/curr/next recursion as the source String.Iterator loop; tabulating all
  suffix results does not add an output. VERINAB61Loop selects the unique
  result at an arbitrary valid iterator position, and VERINAB61AllDigits
  invokes it at the initial iterator position zero. Thus the executable
  result is fixed independently of the postcondition and admits no additional
  outputs.

  VERINAB61Pre is the source True precondition on typed String inputs.
  VERINAB61Post preserves the source equivalence between a true result and
  every character in String.toList satisfying isDigit; the indexed universal
  is equivalent to the source element-membership universal, including for
  repeated characters and the empty string. The proof-valued precondition
  arguments to the implementation and postcondition are computationally and
  propositionally unused beyond the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB61Char VERINAB61IsDigit VERINAB61ToCharList
  VERINAB61LoopGraph VERINAB61Loop
  VERINAB61Pre VERINAB61AllDigits VERINAB61Post
$.

verinab61-char-syntax
  $a class VERINAB61Char $.
verinab61-is-digit-syntax
  $a class ( VERINAB61IsDigit A ) $.
verinab61-to-char-list-syntax
  $a class ( VERINAB61ToCharList A ) $.
verinab61-loop-graph-syntax
  $a wff ( VERINAB61LoopGraph A B C ) $.
verinab61-loop-syntax
  $a class ( VERINAB61Loop A B ) $.
verinab61-precondition-syntax
  $a wff ( VERINAB61Pre A ) $.
verinab61-program-syntax
  $a class ( VERINAB61AllDigits A ) $.
verinab61-postcondition-syntax
  $a wff ( VERINAB61Post A B ) $.

verinab61-char-definition $a |- VERINAB61Char =
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

verinab61-is-digit-definition $a |- (
  VERINAB61IsDigit A
) = if (
  (
    ; 4 8 <_ A
    /\
    A <_ ; 5 7
  ) ,
  1 ,
  0
) $.

verinab61-to-char-list-definition $a |- (
  VERINAB61ToCharList A
) = A $.

${
  $d k t A B C $.

  verinab61-loop-graph-definition $a |- (
    VERINAB61LoopGraph A B C
  ) <-> (
    (
      (
        (
          A e. Word VERINAB61Char
          /\
          B e. NN0
        )
        /\
        B <_ ( # ` A )
      )
      /\
      C e. { 0 , 1 }
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
              ( VERINAB61IsDigit ( A ` k ) ) = 1 ,
              ( t ` ( k + 1 ) ) ,
              0
            )
          /\
          C = ( t ` B )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab61-loop-definition $a |- (
    VERINAB61Loop A B
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINAB61LoopGraph A B y )
  ) $.
$}

verinab61-precondition-definition $a |- (
  VERINAB61Pre A
) <-> (
  A e. Word VERINAB61Char
) $.

verinab61-program-definition $a |- (
  VERINAB61AllDigits A
) = (
  VERINAB61Loop A 0
) $.

${
  $d i A B $.

  verinab61-postcondition-definition $a |- (
    VERINAB61Post A B
  ) <-> (
    (
      A e. Word VERINAB61Char
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      B = 1
      <->
      A. i e. (
        0 ..^ ( # ` ( VERINAB61ToCharList A ) )
      )
        (
          VERINAB61IsDigit
            ( ( VERINAB61ToCharList A ) ` i )
        ) = 1
    )
  ) $.
$}

verina-basic-61-all-digits $a |-
  A. s e. Word VERINAB61Char
    (
      ( VERINAB61Pre s )
      ->
      (
        VERINAB61Post
          s
          ( VERINAB61AllDigits s )
      )
    )
$.
