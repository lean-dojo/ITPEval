$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_21, catalog title isPalindrome: the exact two-method
  executable palindrome test on an arbitrary Unicode string, together with
  its Boolean correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA21Char is exactly the Unicode scalar-value domain represented by
  Lean's Char: natural numbers below 1114112 excluding the surrogate interval
  55296 through 57343. Word VERINA21Char therefore represents arbitrary Lean
  strings extensionally through String.toList, and word length is
  String.length.

  VERINA21CheckContinue is exactly the recursive branch of the local
  checkIndices helper: while left is below right, both indices are valid, and
  the indexed characters agree, it increments left and decrements right.
  VERINA21CheckStop is exactly either the true left-at-or-past-right base case
  or any false lookup/mismatch case. VERINA21CheckGraph records the complete
  finite execution trace, and VERINA21CheckIndices selects its unique Boolean
  result.

  VERINA21ReverseGraph reverses every finite character word exactly.
  Consequently VERINA21ReverseList is both the result of the source
  reverseList helper called with the empty accumulator and the value of the
  List.reverse operation used in the postcondition.

  VERINA21ApproachOne and VERINA21ApproachTwo are the source let-bound Boolean
  computations. VERINA21IsPalindrome preserves the explicit length-at-most-one
  branch and otherwise returns their Boolean conjunction. VERINA21Pre is the
  source True precondition together with the String input type. VERINA21Post
  reproduces both source implications, including the nonempty requirement in
  the false-result case. The proof-valued precondition argument is
  computationally unused and is omitted from the target function. The final
  $a declaration is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA21Char
  VERINA21CheckContinue VERINA21CheckStop
  VERINA21CheckGraph VERINA21CheckIndices
  VERINA21ReverseGraph VERINA21ReverseList
  VERINA21ApproachOne VERINA21ApproachTwo
  VERINA21Pre VERINA21IsPalindrome VERINA21Post
$.

verina21-char-syntax
  $a class VERINA21Char $.
verina21-check-continue-syntax
  $a wff ( VERINA21CheckContinue A B C ) $.
verina21-check-stop-syntax
  $a wff ( VERINA21CheckStop A B C ) $.
verina21-check-graph-syntax
  $a wff ( VERINA21CheckGraph A B C D ) $.
verina21-check-indices-syntax
  $a class ( VERINA21CheckIndices A B C ) $.
verina21-reverse-graph-syntax
  $a wff ( VERINA21ReverseGraph A B ) $.
verina21-reverse-list-syntax
  $a class ( VERINA21ReverseList A ) $.
verina21-approach-one-syntax
  $a class ( VERINA21ApproachOne A ) $.
verina21-approach-two-syntax
  $a class ( VERINA21ApproachTwo A ) $.
verina21-precondition-syntax
  $a wff ( VERINA21Pre A ) $.
verina21-is-palindrome-syntax
  $a class ( VERINA21IsPalindrome A ) $.
verina21-postcondition-syntax
  $a wff ( VERINA21Post A B ) $.

verina21-char-definition $a |- VERINA21Char =
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

verina21-check-continue-definition $a |- (
  VERINA21CheckContinue A B C
) <-> (
  (
    (
      A e. Word VERINA21Char
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
      ( 1st ` B ) < ( # ` A )
    )
    /\
    (
      (
        ( 2nd ` B ) < ( # ` A )
        /\
        ( A ` ( 1st ` B ) ) = ( A ` ( 2nd ` B ) )
      )
      /\
      C = <.
        ( ( 1st ` B ) + 1 ) ,
        ( ( 2nd ` B ) - 1 )
      >.
    )
  )
) $.

verina21-check-stop-definition $a |- (
  VERINA21CheckStop A B C
) <-> (
  (
    (
      A e. Word VERINA21Char
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
          ( # ` A ) <_ ( 1st ` B )
          \/
          ( # ` A ) <_ ( 2nd ` B )
          \/
          ( A ` ( 1st ` B ) ) =/= ( A ` ( 2nd ` B ) )
        )
      )
    )
  )
) $.

${
  $d i k t A B C D $.

  verina21-check-graph-definition $a |- (
    VERINA21CheckGraph A B C D
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. NN0
      )
      /\
      (
        C e. Word VERINA21Char
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
              VERINA21CheckContinue
                C
                ( t ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          (
            VERINA21CheckStop
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

  verina21-check-indices-definition $a |- (
    VERINA21CheckIndices A B C
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA21CheckGraph A B C y )
  ) $.
$}

${
  $d i A B $.

  verina21-reverse-graph-definition $a |- (
    VERINA21ReverseGraph A B
  ) <-> (
    (
      A e. Word VERINA21Char
      /\
      B e. Word VERINA21Char
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

  verina21-reverse-list-definition $a |- (
    VERINA21ReverseList A
  ) = (
    iota_ y e. Word VERINA21Char
      ( VERINA21ReverseGraph A y )
  ) $.
$}

verina21-approach-one-definition $a |- (
  VERINA21ApproachOne A
) = (
  VERINA21CheckIndices
    0
    ( ( # ` A ) - 1 )
    A
) $.

verina21-approach-two-definition $a |- (
  VERINA21ApproachTwo A
) = if (
  A = ( VERINA21ReverseList A ) ,
  1 ,
  0
) $.

verina21-precondition-definition $a |- (
  VERINA21Pre A
) <-> (
  A e. Word VERINA21Char
) $.

verina21-is-palindrome-definition $a |- (
  VERINA21IsPalindrome A
) = if (
  ( # ` A ) <_ 1 ,
  1 ,
  if (
    (
      ( VERINA21ApproachOne A ) = 1
      /\
      ( VERINA21ApproachTwo A ) = 1
    ) ,
    1 ,
    0
  )
) $.

verina21-postcondition-definition $a |- (
  VERINA21Post A B
) <-> (
  (
    A e. Word VERINA21Char
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    (
      B = 1
      ->
      A = ( VERINA21ReverseList A )
    )
    /\
    (
      B = 0
      ->
      (
        A =/= (/)
        /\
        A =/= ( VERINA21ReverseList A )
      )
    )
  )
) $.

verina-advanced-21-is-palindrome
  $a |- A. w e. Word VERINA21Char
    (
      ( VERINA21Pre w )
      ->
      (
        VERINA21Post
          w
          ( VERINA21IsPalindrome w )
      )
    )
  $.
