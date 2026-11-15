$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_66 (verina__metamath__verina_advanced_66), catalog title
  reverseWords: the exact Unicode-string program splits at literal spaces,
  removes empty fields, reverses the remaining words, and rejoins them with
  single spaces, together with its correctness contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  VERINA66Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINA66Char represents arbitrary Lean strings extensionally through
  their character lists. VERINA66Space is the one-character string containing
  ASCII space, code point 32. VERINA66Concat is exact string concatenation.

  VERINA66SplitOnSpaceGraph records every literal-space position in increasing
  order and makes the intervening character intervals the output fields.
  Thus VERINA66SplitOnSpace is exactly String.splitOn " ", including empty
  fields from empty input and leading, trailing, or repeated spaces.
  VERINA66FilterNonEmpty selects every nonempty field in stable order, exactly
  reproducing both the source-local filterNonEmpty recursion and the List.filter
  operation in the postcondition. VERINA66Reverse is exact list reversal.

  VERINA66JoinWithSpaceGraph records the complete deterministic right-recursive
  execution of the source-local joinWithSpace helper: the empty list yields
  the empty string, a singleton yields its only word, and longer lists insert
  one VERINA66Space between the head and the recursively joined tail.
  VERINA66IntercalateSpace is the same computation as String.intercalate " ".
  VERINA66ReverseWords explicitly composes split, filter, reverse, and join, so
  its result is fixed independently of the postcondition.

  VERINA66Pre is the source True precondition on typed String inputs.
  VERINA66Post preserves the source existential word list, its equality to the
  filtered split result, and the result equality to intercalation of the
  reversed list. The proof-valued precondition argument is computationally
  and propositionally unused and is represented by the explicit antecedent of
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition, and this database has no $p declaration.
$)

$c
  VERINA66Char
  VERINA66SpaceGraph VERINA66Space
  VERINA66ConcatGraph VERINA66Concat
  VERINA66SplitOnSpaceGraph VERINA66SplitOnSpace
  VERINA66FilterNonEmptyGraph VERINA66FilterNonEmpty
  VERINA66ReverseGraph VERINA66Reverse
  VERINA66JoinWithSpaceGraph VERINA66JoinWithSpace
  VERINA66IntercalateSpace
  VERINA66Pre VERINA66ReverseWords VERINA66Post
$.

verina66-char-syntax
  $a class VERINA66Char $.
verina66-space-graph-syntax
  $a wff ( VERINA66SpaceGraph A ) $.
verina66-space-syntax
  $a class VERINA66Space $.
verina66-concat-graph-syntax
  $a wff ( VERINA66ConcatGraph A B C ) $.
verina66-concat-syntax
  $a class ( VERINA66Concat A B ) $.
verina66-split-on-space-graph-syntax
  $a wff ( VERINA66SplitOnSpaceGraph A B ) $.
verina66-split-on-space-syntax
  $a class ( VERINA66SplitOnSpace A ) $.
verina66-filter-nonempty-graph-syntax
  $a wff ( VERINA66FilterNonEmptyGraph A B ) $.
verina66-filter-nonempty-syntax
  $a class ( VERINA66FilterNonEmpty A ) $.
verina66-reverse-graph-syntax
  $a wff ( VERINA66ReverseGraph A B ) $.
verina66-reverse-syntax
  $a class ( VERINA66Reverse A ) $.
verina66-join-with-space-graph-syntax
  $a wff ( VERINA66JoinWithSpaceGraph A B ) $.
verina66-join-with-space-syntax
  $a class ( VERINA66JoinWithSpace A ) $.
verina66-intercalate-space-syntax
  $a class ( VERINA66IntercalateSpace A ) $.
verina66-precondition-syntax
  $a wff ( VERINA66Pre A ) $.
verina66-program-syntax
  $a class ( VERINA66ReverseWords A ) $.
verina66-postcondition-syntax
  $a wff ( VERINA66Post A B ) $.

verina66-char-definition $a |- VERINA66Char =
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

verina66-space-graph-definition $a |- (
  VERINA66SpaceGraph A
) <-> (
  A e. Word VERINA66Char
  /\
  (
    ( # ` A ) = 1
    /\
    ( A ` 0 ) = ; 3 2
  )
) $.

${
  $d x y $.

  verina66-space-definition $a |- VERINA66Space =
    (
      iota_ y e. Word VERINA66Char
        ( VERINA66SpaceGraph y )
    ) $.
$}

${
  $d i j A B C $.

  verina66-concat-graph-definition $a |- (
    VERINA66ConcatGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA66Char
        /\
        B e. Word VERINA66Char
      )
      /\
      C e. Word VERINA66Char
    )
    /\
    (
      ( # ` C ) = ( ( # ` A ) + ( # ` B ) )
      /\
      (
        A. i e. ( 0 ..^ ( # ` A ) )
          ( C ` i ) = ( A ` i )
        /\
        A. j e. ( 0 ..^ ( # ` B ) )
          ( C ` ( ( # ` A ) + j ) ) = ( B ` j )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina66-concat-definition $a |- (
    VERINA66Concat A B
  ) = (
    iota_ y e. Word VERINA66Char
      ( VERINA66ConcatGraph A B y )
  ) $.
$}

${
  $d i j k p r s A B $.

  verina66-split-on-space-graph-definition $a |- (
    VERINA66SplitOnSpaceGraph A B
  ) <-> (
    (
      A e. Word VERINA66Char
      /\
      B e. Word ( Word VERINA66Char )
    )
    /\
    E. p e. Word NN0
      (
        ( # ` B ) = ( ( # ` p ) + 1 )
        /\
        (
          (
            A. r e. ( 0 ..^ ( # ` p ) )
              (
                ( p ` r ) < ( # ` A )
                /\
                ( A ` ( p ` r ) ) = ; 3 2
              )
            /\
            A. r e. ( 0 ..^ ( # ` p ) )
              A. s e. ( 0 ..^ ( # ` p ) )
                (
                  r < s
                  ->
                  ( p ` r ) < ( p ` s )
                )
          )
          /\
          (
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                ( A ` i ) = ; 3 2
                ->
                E. r e. ( 0 ..^ ( # ` p ) )
                  ( p ` r ) = i
              )
            /\
            A. j e. ( 0 ..^ ( # ` B ) )
              (
                (
                  # ` ( B ` j )
                ) = (
                  if (
                    j < ( # ` p ) ,
                    ( p ` j ) ,
                    ( # ` A )
                  )
                  -
                  if (
                    j = 0 ,
                    0 ,
                    ( ( p ` ( j - 1 ) ) + 1 )
                  )
                )
                /\
                A. k e. ( 0 ..^ ( # ` ( B ` j ) ) )
                  (
                    ( B ` j ) ` k
                  ) = (
                    A ` (
                      if (
                        j = 0 ,
                        0 ,
                        ( ( p ` ( j - 1 ) ) + 1 )
                      )
                      + k
                    )
                  )
              )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina66-split-on-space-definition $a |- (
    VERINA66SplitOnSpace A
  ) = (
    iota_ y e. Word ( Word VERINA66Char )
      ( VERINA66SplitOnSpaceGraph A y )
  ) $.
$}

${
  $d i j k p A B $.

  verina66-filter-nonempty-graph-definition $a |- (
    VERINA66FilterNonEmptyGraph A B
  ) <-> (
    (
      A e. Word ( Word VERINA66Char )
      /\
      B e. Word ( Word VERINA66Char )
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` B )
        /\
        (
          A. j e. ( 0 ..^ ( # ` B ) )
            (
              (
                ( p ` j ) < ( # ` A )
                /\
                ( A ` ( p ` j ) ) =/= (/)
              )
              /\
              ( B ` j ) = ( A ` ( p ` j ) )
            )
          /\
          (
            A. j e. ( 0 ..^ ( # ` B ) )
              A. k e. ( 0 ..^ ( # ` B ) )
                (
                  j < k
                  ->
                  ( p ` j ) < ( p ` k )
                )
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                ( A ` i ) =/= (/)
                ->
                E. j e. ( 0 ..^ ( # ` B ) )
                  ( p ` j ) = i
              )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina66-filter-nonempty-definition $a |- (
    VERINA66FilterNonEmpty A
  ) = (
    iota_ y e. Word ( Word VERINA66Char )
      ( VERINA66FilterNonEmptyGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina66-reverse-graph-definition $a |- (
    VERINA66ReverseGraph A B
  ) <-> (
    (
      A e. Word ( Word VERINA66Char )
      /\
      B e. Word ( Word VERINA66Char )
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

  verina66-reverse-definition $a |- (
    VERINA66Reverse A
  ) = (
    iota_ y e. Word ( Word VERINA66Char )
      ( VERINA66ReverseGraph A y )
  ) $.
$}

${
  $d i t A B $.

  verina66-join-with-space-graph-definition $a |- (
    VERINA66JoinWithSpaceGraph A B
  ) <-> (
    (
      A e. Word ( Word VERINA66Char )
      /\
      B e. Word VERINA66Char
    )
    /\
    E. t e. Word ( Word VERINA66Char )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` ( # ` A ) ) = (/)
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              t ` i
            ) = if (
              i = ( ( # ` A ) - 1 ) ,
              ( A ` i ) ,
              (
                VERINA66Concat
                  ( A ` i )
                  (
                    VERINA66Concat
                      VERINA66Space
                      ( t ` ( i + 1 ) )
                  )
              )
            )
          /\
          B = ( t ` 0 )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina66-join-with-space-definition $a |- (
    VERINA66JoinWithSpace A
  ) = (
    iota_ y e. Word VERINA66Char
      ( VERINA66JoinWithSpaceGraph A y )
  ) $.
$}

verina66-intercalate-space-definition $a |- (
  VERINA66IntercalateSpace A
) = (
  VERINA66JoinWithSpace A
) $.

verina66-precondition-definition $a |- (
  VERINA66Pre A
) <-> (
  A e. Word VERINA66Char
) $.

verina66-program-definition $a |- (
  VERINA66ReverseWords A
) = (
  VERINA66JoinWithSpace
    (
      VERINA66Reverse
        (
          VERINA66FilterNonEmpty
            ( VERINA66SplitOnSpace A )
        )
    )
) $.

${
  $d w A B $.

  verina66-postcondition-definition $a |- (
    VERINA66Post A B
  ) <-> (
    (
      A e. Word VERINA66Char
      /\
      B e. Word VERINA66Char
    )
    /\
    E. w e. Word ( Word VERINA66Char )
      (
        w = (
          VERINA66FilterNonEmpty
            ( VERINA66SplitOnSpace A )
        )
        /\
        B = (
          VERINA66IntercalateSpace
            ( VERINA66Reverse w )
        )
      )
  ) $.
$}

verina-advanced-66-reverse-words
  $a |- A. s e. Word VERINA66Char
    (
      ( VERINA66Pre s )
      ->
      (
        VERINA66Post
          s
          ( VERINA66ReverseWords s )
      )
    )
  $.
