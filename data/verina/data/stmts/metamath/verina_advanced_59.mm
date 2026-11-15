$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_59 (verina__metamath__verina_advanced_59), catalog title
  palindromeIgnoreNonAlnum: the exact program filters ASCII alphanumeric
  characters from an arbitrary Unicode string, lowercases them, and runs its
  two-index Boolean palindrome checker, together with the complete correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA59Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINA59Char represents arbitrary Lean strings extensionally through
  String.data. VERINA59IsAlpha, VERINA59IsDigit, VERINA59IsAlnum, and
  VERINA59ToLower reproduce the source Char operations exactly: their tests
  use the basic-Latin ASCII ranges and lowercasing adds 32 only for A through
  Z.

  VERINA59FilterGraph retains exactly the alphanumeric input characters in
  their original order. VERINA59MapLowerGraph lowercases every retained
  character, so VERINA59Cleaned is exactly the source filter followed by map.

  VERINA59None, VERINA59Some, VERINA59OptionChar, and VERINA59GetOption encode
  List.get? exactly, including none outside the word. VERINA59CheckContinue
  and VERINA59CheckStop reproduce the local recursive check branches.
  VERINA59CheckGraph records the complete deterministic execution trace from
  arbitrary natural indices, including the source equality test on option
  values, and VERINA59Check selects its unique Boolean result.
  VERINA59EndIndex preserves the explicit empty-list branch, and
  VERINA59PalindromeIgnoreNonAlnum composes the exact cleaned word with the
  checker starting at zero and that end index. Its output is therefore fixed
  independently of the postcondition.

  VERINA59ReverseGraph is exact list reversal. VERINA59Pre is the source True
  precondition on typed string inputs. VERINA59Post is the source conditional
  equality-versus-inequality contract for the cleaned word and its reversal.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent of the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition, and this database has no $p declaration.
$)

$c
  VERINA59Char
  VERINA59IsUpper VERINA59IsLower VERINA59IsAlpha VERINA59IsDigit
  VERINA59IsAlnum VERINA59ToLower
  VERINA59FilterGraph VERINA59Filter
  VERINA59MapLowerGraph VERINA59MapLower VERINA59Cleaned
  VERINA59None VERINA59Some VERINA59OptionChar VERINA59GetOption
  VERINA59CheckContinue VERINA59CheckStop
  VERINA59CheckGraph VERINA59Check
  VERINA59EndIndex VERINA59PalindromeIgnoreNonAlnum
  VERINA59ReverseGraph VERINA59Reverse
  VERINA59Pre VERINA59Post
$.

verina59-char-syntax
  $a class VERINA59Char $.
verina59-is-upper-syntax
  $a class ( VERINA59IsUpper A ) $.
verina59-is-lower-syntax
  $a class ( VERINA59IsLower A ) $.
verina59-is-alpha-syntax
  $a class ( VERINA59IsAlpha A ) $.
verina59-is-digit-syntax
  $a class ( VERINA59IsDigit A ) $.
verina59-is-alnum-syntax
  $a class ( VERINA59IsAlnum A ) $.
verina59-to-lower-syntax
  $a class ( VERINA59ToLower A ) $.
verina59-filter-graph-syntax
  $a wff ( VERINA59FilterGraph A B ) $.
verina59-filter-syntax
  $a class ( VERINA59Filter A ) $.
verina59-map-lower-graph-syntax
  $a wff ( VERINA59MapLowerGraph A B ) $.
verina59-map-lower-syntax
  $a class ( VERINA59MapLower A ) $.
verina59-cleaned-syntax
  $a class ( VERINA59Cleaned A ) $.
verina59-none-syntax
  $a class VERINA59None $.
verina59-some-syntax
  $a class ( VERINA59Some A ) $.
verina59-option-char-syntax
  $a class VERINA59OptionChar $.
verina59-get-option-syntax
  $a class ( VERINA59GetOption A B ) $.
verina59-check-continue-syntax
  $a wff ( VERINA59CheckContinue A B C ) $.
verina59-check-stop-syntax
  $a wff ( VERINA59CheckStop A B C ) $.
verina59-check-graph-syntax
  $a wff ( VERINA59CheckGraph A B C D ) $.
verina59-check-syntax
  $a class ( VERINA59Check A B C ) $.
verina59-end-index-syntax
  $a class ( VERINA59EndIndex A ) $.
verina59-program-syntax
  $a class ( VERINA59PalindromeIgnoreNonAlnum A ) $.
verina59-reverse-graph-syntax
  $a wff ( VERINA59ReverseGraph A B ) $.
verina59-reverse-syntax
  $a class ( VERINA59Reverse A ) $.
verina59-precondition-syntax
  $a wff ( VERINA59Pre A ) $.
verina59-postcondition-syntax
  $a wff ( VERINA59Post A B ) $.

verina59-char-definition $a |- VERINA59Char =
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

verina59-is-upper-definition $a |- (
  VERINA59IsUpper A
) = if (
  (
    ; 6 5 <_ A
    /\
    A <_ ; 9 0
  ) ,
  1 ,
  0
) $.

verina59-is-lower-definition $a |- (
  VERINA59IsLower A
) = if (
  (
    ; 9 7 <_ A
    /\
    A <_ ; ; 1 2 2
  ) ,
  1 ,
  0
) $.

verina59-is-alpha-definition $a |- (
  VERINA59IsAlpha A
) = if (
  (
    ( VERINA59IsUpper A ) = 1
    \/
    ( VERINA59IsLower A ) = 1
  ) ,
  1 ,
  0
) $.

verina59-is-digit-definition $a |- (
  VERINA59IsDigit A
) = if (
  (
    ; 4 8 <_ A
    /\
    A <_ ; 5 7
  ) ,
  1 ,
  0
) $.

verina59-is-alnum-definition $a |- (
  VERINA59IsAlnum A
) = if (
  (
    ( VERINA59IsAlpha A ) = 1
    \/
    ( VERINA59IsDigit A ) = 1
  ) ,
  1 ,
  0
) $.

verina59-to-lower-definition $a |- (
  VERINA59ToLower A
) = if (
  ( VERINA59IsUpper A ) = 1 ,
  ( A + ; 3 2 ) ,
  A
) $.

${
  $d i j k p A B $.

  verina59-filter-graph-definition $a |- (
    VERINA59FilterGraph A B
  ) <-> (
    (
      A e. Word VERINA59Char
      /\
      B e. Word VERINA59Char
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` B )
        /\
        (
          A. i e. ( 0 ..^ ( # ` B ) )
            (
              (
                ( p ` i ) < ( # ` A )
                /\
                ( VERINA59IsAlnum ( A ` ( p ` i ) ) ) = 1
              )
              /\
              ( B ` i ) = ( A ` ( p ` i ) )
            )
          /\
          (
            A. i e. ( 0 ..^ ( # ` B ) )
              A. j e. ( 0 ..^ ( # ` B ) )
                (
                  i < j
                  ->
                  ( p ` i ) < ( p ` j )
                )
            /\
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                ( VERINA59IsAlnum ( A ` k ) ) = 1
                ->
                E. i e. ( 0 ..^ ( # ` B ) )
                  ( p ` i ) = k
              )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina59-filter-definition $a |- (
    VERINA59Filter A
  ) = (
    iota_ y e. Word VERINA59Char
      ( VERINA59FilterGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina59-map-lower-graph-definition $a |- (
    VERINA59MapLowerGraph A B
  ) <-> (
    (
      A e. Word VERINA59Char
      /\
      B e. Word VERINA59Char
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( B ` i ) = ( VERINA59ToLower ( A ` i ) )
    )
  ) $.
$}

${
  $d y A $.

  verina59-map-lower-definition $a |- (
    VERINA59MapLower A
  ) = (
    iota_ y e. Word VERINA59Char
      ( VERINA59MapLowerGraph A y )
  ) $.
$}

verina59-cleaned-definition $a |- (
  VERINA59Cleaned A
) = (
  VERINA59MapLower
    ( VERINA59Filter A )
) $.

verina59-none-definition $a |- VERINA59None = (/) $.

verina59-some-definition $a |- (
  VERINA59Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina59-option-char-definition $a |- VERINA59OptionChar =
    { x |
      (
        x = VERINA59None
        \/
        E. y e. VERINA59Char
          x = ( VERINA59Some y )
      )
    } $.
$}

verina59-get-option-definition $a |- (
  VERINA59GetOption A B
) = if (
  B < ( # ` A ) ,
  ( VERINA59Some ( A ` B ) ) ,
  VERINA59None
) $.

verina59-check-continue-definition $a |- (
  VERINA59CheckContinue A B C
) <-> (
  (
    (
      A e. Word VERINA59Char
      /\
      B e. ( NN0 X. NN0 )
    )
    /\
    C e. ( NN0 X. NN0 )
  )
  /\
  (
    (
      ( 1st ` B ) < ( 2nd ` B )
      /\
      (
        VERINA59GetOption A ( 1st ` B )
      ) = (
        VERINA59GetOption A ( 2nd ` B )
      )
    )
    /\
    C = <.
      ( ( 1st ` B ) + 1 ) ,
      ( ( 2nd ` B ) - 1 )
    >.
  )
) $.

verina59-check-stop-definition $a |- (
  VERINA59CheckStop A B C
) <-> (
  (
    (
      A e. Word VERINA59Char
      /\
      B e. ( NN0 X. NN0 )
    )
    /\
    C e. { 0 , 1 }
  )
  /\
  (
    (
      C = 1
      /\
      ( 2nd ` B ) <_ ( 1st ` B )
    )
    \/
    (
      C = 0
      /\
      (
        ( 1st ` B ) < ( 2nd ` B )
        /\
        (
          VERINA59GetOption A ( 1st ` B )
        ) =/= (
          VERINA59GetOption A ( 2nd ` B )
        )
      )
    )
  )
) $.

${
  $d i k t A B C D $.

  verina59-check-graph-definition $a |- (
    VERINA59CheckGraph A B C D
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. NN0
      )
      /\
      (
        C e. Word VERINA59Char
        /\
        D e. { 0 , 1 }
      )
    )
    /\
    E. k e. NN0 E. t e. Word ( NN0 X. NN0 )
      (
        (
          ( # ` t ) = ( k + 1 )
          /\
          ( t ` 0 ) = <. A , B >.
        )
        /\
        (
          A. i e. ( 0 ..^ k )
            (
              VERINA59CheckContinue
                C
                ( t ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          (
            VERINA59CheckStop
              C
              ( t ` k )
              D
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verina59-check-definition $a |- (
    VERINA59Check A B C
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA59CheckGraph A B C y )
  ) $.
$}

verina59-end-index-definition $a |- (
  VERINA59EndIndex A
) = if (
  ( # ` A ) = 0 ,
  0 ,
  ( ( # ` A ) - 1 )
) $.

verina59-program-definition $a |- (
  VERINA59PalindromeIgnoreNonAlnum A
) = (
  VERINA59Check
    0
    ( VERINA59EndIndex ( VERINA59Cleaned A ) )
    ( VERINA59Cleaned A )
) $.

${
  $d i A B $.

  verina59-reverse-graph-definition $a |- (
    VERINA59ReverseGraph A B
  ) <-> (
    (
      A e. Word VERINA59Char
      /\
      B e. Word VERINA59Char
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

  verina59-reverse-definition $a |- (
    VERINA59Reverse A
  ) = (
    iota_ y e. Word VERINA59Char
      ( VERINA59ReverseGraph A y )
  ) $.
$}

verina59-precondition-definition $a |- (
  VERINA59Pre A
) <-> (
  A e. Word VERINA59Char
) $.

verina59-postcondition-definition $a |- (
  VERINA59Post A B
) <-> (
  (
    A e. Word VERINA59Char
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    (
      B = 1
      ->
      (
        VERINA59Cleaned A
      ) = (
        VERINA59Reverse
          ( VERINA59Cleaned A )
      )
    )
    /\
    (
      B = 0
      ->
      (
        VERINA59Cleaned A
      ) =/= (
        VERINA59Reverse
          ( VERINA59Cleaned A )
      )
    )
  )
) $.

verina-advanced-59-palindrome-ignore-non-alnum
  $a |- A. w e. Word VERINA59Char
    (
      ( VERINA59Pre w )
      ->
      (
        VERINA59Post
          w
          ( VERINA59PalindromeIgnoreNonAlnum w )
      )
    )
  $.
