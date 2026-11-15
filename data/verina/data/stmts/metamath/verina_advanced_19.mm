$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_19, catalog title isCleanPalindrome: exact ASCII
  alphabetic filtering and lowercasing of an arbitrary Unicode string,
  followed by a Boolean palindrome test and its correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA19Char is exactly the Unicode scalar-value domain represented by
  Lean's Char: natural numbers below 1114112 excluding the surrogate interval
  55296 through 57343. Word VERINA19Char therefore represents arbitrary Lean
  strings extensionally through String.toList, without restricting inputs to
  ASCII.

  VERINA19IsUpper, VERINA19IsLower, and VERINA19IsAlpha are the source
  Boolean helpers, using precisely the ASCII ranges A--Z and a--z.
  VERINA19ToLower adds 32 exactly in the uppercase case; this agrees with
  Char.ofNat because every resulting code is a valid lowercase ASCII scalar.
  VERINA19None, VERINA19Some, and VERINA19OptionChar faithfully encode
  Option Char, and VERINA19NormalizeChar is the source optional helper.

  VERINA19NormalizeGraph retains exactly, in original order, all input
  positions where normalizeChar is non-none and stores the corresponding
  lowercase characters. Thus VERINA19NormalizeString is exactly the source
  foldr computation, not an output selected from the postcondition.
  VERINA19ReverseGraph reverses every finite character word exactly, and
  VERINA19ReverseList is the source reverseList helper.

  VERINA19IsCleanPalindrome is the executable Boolean equality test on the
  normalized word and its reversal. VERINA19Pre is the source True
  precondition together with the String input type. VERINA19Post reproduces
  both result implications in the source postcondition. The proof-valued
  precondition argument is computationally unused and is omitted from the
  target function. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and this
  database has no proof declaration.
$)

$c
  VERINA19Char
  VERINA19IsUpper VERINA19IsLower VERINA19IsAlpha
  VERINA19ToLower
  VERINA19None VERINA19Some VERINA19OptionChar
  VERINA19NormalizeChar
  VERINA19NormalizeGraph VERINA19NormalizeString
  VERINA19ReverseGraph VERINA19ReverseList
  VERINA19Pre VERINA19IsCleanPalindrome VERINA19Post
$.

verina19-char-syntax
  $a class VERINA19Char $.
verina19-is-upper-syntax
  $a class ( VERINA19IsUpper A ) $.
verina19-is-lower-syntax
  $a class ( VERINA19IsLower A ) $.
verina19-is-alpha-syntax
  $a class ( VERINA19IsAlpha A ) $.
verina19-to-lower-syntax
  $a class ( VERINA19ToLower A ) $.
verina19-none-syntax
  $a class VERINA19None $.
verina19-some-syntax
  $a class ( VERINA19Some A ) $.
verina19-option-char-syntax
  $a class VERINA19OptionChar $.
verina19-normalize-char-syntax
  $a class ( VERINA19NormalizeChar A ) $.
verina19-normalize-graph-syntax
  $a wff ( VERINA19NormalizeGraph A B ) $.
verina19-normalize-string-syntax
  $a class ( VERINA19NormalizeString A ) $.
verina19-reverse-graph-syntax
  $a wff ( VERINA19ReverseGraph A B ) $.
verina19-reverse-list-syntax
  $a class ( VERINA19ReverseList A ) $.
verina19-precondition-syntax
  $a wff ( VERINA19Pre A ) $.
verina19-is-clean-palindrome-syntax
  $a class ( VERINA19IsCleanPalindrome A ) $.
verina19-postcondition-syntax
  $a wff ( VERINA19Post A B ) $.

verina19-char-definition $a |- VERINA19Char =
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

verina19-is-upper-definition $a |- (
  VERINA19IsUpper A
) = if (
  (
    ; 6 5 <_ A
    /\
    A <_ ; 9 0
  ) ,
  1 ,
  0
) $.

verina19-is-lower-definition $a |- (
  VERINA19IsLower A
) = if (
  (
    ; 9 7 <_ A
    /\
    A <_ ; ; 1 2 2
  ) ,
  1 ,
  0
) $.

verina19-is-alpha-definition $a |- (
  VERINA19IsAlpha A
) = if (
  (
    ( VERINA19IsUpper A ) = 1
    \/
    ( VERINA19IsLower A ) = 1
  ) ,
  1 ,
  0
) $.

verina19-to-lower-definition $a |- (
  VERINA19ToLower A
) = if (
  ( VERINA19IsUpper A ) = 1 ,
  ( A + ; 3 2 ) ,
  A
) $.

verina19-none-definition $a |- VERINA19None = (/) $.

verina19-some-definition $a |- (
  VERINA19Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina19-option-char-definition $a |- VERINA19OptionChar =
    { x |
      (
        x = VERINA19None
        \/
        E. y e. VERINA19Char
          x = ( VERINA19Some y )
      )
    } $.
$}

verina19-normalize-char-definition $a |- (
  VERINA19NormalizeChar A
) = if (
  ( VERINA19IsAlpha A ) = 1 ,
  ( VERINA19Some ( VERINA19ToLower A ) ) ,
  VERINA19None
) $.

${
  $d i j k p A B $.

  verina19-normalize-graph-definition $a |- (
    VERINA19NormalizeGraph A B
  ) <-> (
    (
      A e. Word VERINA19Char
      /\
      B e. Word VERINA19Char
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` B )
        /\
        (
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              ( p ` i ) < ( # ` A )
              /\
              (
                VERINA19NormalizeChar
                  ( A ` ( p ` i ) )
              ) = (
                VERINA19Some ( B ` i )
              )
            )
          /\
          (
            A. i e. ( 0 ..^ ( # ` p ) )
              A. j e. ( 0 ..^ ( # ` p ) )
                (
                  i < j
                  ->
                  ( p ` i ) < ( p ` j )
                )
            /\
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                (
                  VERINA19NormalizeChar ( A ` k )
                ) =/= VERINA19None
                ->
                E. i e. ( 0 ..^ ( # ` p ) )
                  ( p ` i ) = k
              )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina19-normalize-string-definition $a |- (
    VERINA19NormalizeString A
  ) = (
    iota_ y e. Word VERINA19Char
      ( VERINA19NormalizeGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina19-reverse-graph-definition $a |- (
    VERINA19ReverseGraph A B
  ) <-> (
    (
      A e. Word VERINA19Char
      /\
      B e. Word VERINA19Char
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

  verina19-reverse-list-definition $a |- (
    VERINA19ReverseList A
  ) = (
    iota_ y e. Word VERINA19Char
      ( VERINA19ReverseGraph A y )
  ) $.
$}

verina19-precondition-definition $a |- (
  VERINA19Pre A
) <-> (
  A e. Word VERINA19Char
) $.

verina19-is-clean-palindrome-definition $a |- (
  VERINA19IsCleanPalindrome A
) = if (
  (
    VERINA19NormalizeString A
  ) = (
    VERINA19ReverseList
      ( VERINA19NormalizeString A )
  ) ,
  1 ,
  0
) $.

verina19-postcondition-definition $a |- (
  VERINA19Post A B
) <-> (
  (
    A e. Word VERINA19Char
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    (
      B = 1
      ->
      (
        VERINA19NormalizeString A
      ) = (
        VERINA19ReverseList
          ( VERINA19NormalizeString A )
      )
    )
    /\
    (
      B = 0
      ->
      (
        VERINA19NormalizeString A
      ) =/= (
        VERINA19ReverseList
          ( VERINA19NormalizeString A )
      )
    )
  )
) $.

verina-advanced-19-is-clean-palindrome
  $a |- A. w e. Word VERINA19Char
    (
      ( VERINA19Pre w )
      ->
      (
        VERINA19Post
          w
          ( VERINA19IsCleanPalindrome w )
      )
    )
  $.
