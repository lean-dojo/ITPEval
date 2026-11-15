$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_71 (verina__metamath__verina_advanced_71), catalog title
  shortestBeautifulSubstring: the exact substring enumeration, stable
  filtering, and option-valued minimum fold return the shortest nonempty
  binary substring containing exactly k ones, breaking length ties
  lexicographically, together with the full correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA71Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINA71Char represents arbitrary Lean strings extensionally through
  String.data and String.toList. VERINA71Chars, VERINA71ListToString, and
  VERINA71StringMk are therefore the exact source conversions on this word
  representation. The natural values ; 4 8 and ; 4 9 represent '0' and '1'.

  VERINA71CountOnes is the source foldl countOnes: it is the cardinality of
  precisely the input positions containing '1'. VERINA71Slice is exact
  List.drop followed by List.take, including arbitrary natural arguments.

  VERINA71AllSubstringsGraph reproduces the implementation helper's nested
  List.range/flatMap/map order: starts increase first and, at each start,
  positive lengths increase from one through the remaining suffix length.
  VERINA71CandidatesGraph is the exact stable filter retaining occurrences
  whose countOnes value is k.

  VERINA71LexLT is Lean's lexicographic List Char and String order: a proper
  prefix is smaller, otherwise the first differing Unicode scalar value
  decides. VERINA71IsLexSmaller is the source helper on String.mk results,
  and VERINA71Compare is the implementation's strict length-first order.
  VERINA71BestGraph records the exact left fold from none: the first
  candidate becomes the best, and every later candidate replaces it exactly
  when VERINA71Compare holds. VERINA71ShortestBeautifulSubstring performs
  the source final option match, so its output is fixed independently of the
  postcondition and the graph admits no extra program results.

  VERINA71PostSubstringsGraph separately reproduces the postcondition's
  nested enumeration, including length zero before filtering.
  VERINA71TargetsGraph then performs its countOnes filter, String.asString
  map, and nonempty filter stably and occurrence-by-occurrence.
  VERINA71Post preserves both source disjuncts and the non-strict
  lexicographic tie condition. VERINA71Pre is the complete binary-string
  precondition with typed String and Nat arguments. The proof-valued
  precondition parameters are computationally and propositionally unused and
  are represented by the explicit antecedent of the final correctness
  assertion. Every earlier $a is syntax or a faithful definition required by
  this rendering, and this database has no $p declaration.
$)

$c
  VERINA71Char
  VERINA71Chars VERINA71ListToString VERINA71StringMk
  VERINA71CountOnes VERINA71NatMin
  VERINA71SliceGraph VERINA71Slice
  VERINA71AllSubstringsGraph VERINA71AllSubstrings
  VERINA71CandidatesGraph VERINA71Candidates
  VERINA71LexLT VERINA71LexLE VERINA71IsLexSmaller VERINA71Compare
  VERINA71None VERINA71Some VERINA71OptionString
  VERINA71BestGraph VERINA71Best
  VERINA71Pre VERINA71ShortestBeautifulSubstring
  VERINA71PostSubstringsGraph VERINA71PostSubstrings
  VERINA71TargetsGraph VERINA71Targets
  VERINA71Post
$.

verina71-char-syntax
  $a class VERINA71Char $.
verina71-chars-syntax
  $a class ( VERINA71Chars A ) $.
verina71-list-to-string-syntax
  $a class ( VERINA71ListToString A ) $.
verina71-string-mk-syntax
  $a class ( VERINA71StringMk A ) $.
verina71-count-ones-syntax
  $a class ( VERINA71CountOnes A ) $.
verina71-nat-min-syntax
  $a class ( VERINA71NatMin A B ) $.
verina71-slice-graph-syntax
  $a wff ( VERINA71SliceGraph A B C D ) $.
verina71-slice-syntax
  $a class ( VERINA71Slice A B C ) $.
verina71-all-substrings-graph-syntax
  $a wff ( VERINA71AllSubstringsGraph A B ) $.
verina71-all-substrings-syntax
  $a class ( VERINA71AllSubstrings A ) $.
verina71-candidates-graph-syntax
  $a wff ( VERINA71CandidatesGraph A B C ) $.
verina71-candidates-syntax
  $a class ( VERINA71Candidates A B ) $.
verina71-lex-lt-syntax
  $a wff ( VERINA71LexLT A B ) $.
verina71-lex-le-syntax
  $a wff ( VERINA71LexLE A B ) $.
verina71-is-lex-smaller-syntax
  $a wff ( VERINA71IsLexSmaller A B ) $.
verina71-compare-syntax
  $a wff ( VERINA71Compare A B ) $.
verina71-none-syntax
  $a class VERINA71None $.
verina71-some-syntax
  $a class ( VERINA71Some A ) $.
verina71-option-string-syntax
  $a class VERINA71OptionString $.
verina71-best-graph-syntax
  $a wff ( VERINA71BestGraph A B ) $.
verina71-best-syntax
  $a class ( VERINA71Best A ) $.
verina71-precondition-syntax
  $a wff ( VERINA71Pre A B ) $.
verina71-program-syntax
  $a class ( VERINA71ShortestBeautifulSubstring A B ) $.
verina71-post-substrings-graph-syntax
  $a wff ( VERINA71PostSubstringsGraph A B ) $.
verina71-post-substrings-syntax
  $a class ( VERINA71PostSubstrings A ) $.
verina71-targets-graph-syntax
  $a wff ( VERINA71TargetsGraph A B C ) $.
verina71-targets-syntax
  $a class ( VERINA71Targets A B ) $.
verina71-postcondition-syntax
  $a wff ( VERINA71Post A B C ) $.

verina71-char-definition $a |- VERINA71Char =
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

verina71-chars-definition $a |- (
  VERINA71Chars A
) = A $.

verina71-list-to-string-definition $a |- (
  VERINA71ListToString A
) = A $.

verina71-string-mk-definition $a |- (
  VERINA71StringMk A
) = A $.

${
  $d i A $.

  verina71-count-ones-definition $a |- (
    VERINA71CountOnes A
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( A ` i ) = ; 4 9
    }
  ) $.
$}

verina71-nat-min-definition $a |- (
  VERINA71NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

${
  $d i A B C D $.

  verina71-slice-graph-definition $a |- (
    VERINA71SliceGraph A B C D
  ) <-> (
    (
      (
        A e. Word VERINA71Char
        /\
        B e. NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. Word VERINA71Char
      )
    )
    /\
    (
      (
        # ` D
      ) = (
        VERINA71NatMin
          C
          (
            ( # ` A )
            -
            ( VERINA71NatMin B ( # ` A ) )
          )
      )
      /\
      A. i e. ( 0 ..^ ( # ` D ) )
        (
          D ` i
        ) = (
          A ` (
            ( VERINA71NatMin B ( # ` A ) ) + i
          )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verina71-slice-definition $a |- (
    VERINA71Slice A B C
  ) = (
    iota_ y e. Word VERINA71Char
      ( VERINA71SliceGraph A B C y )
  ) $.
$}

${
  $d i j l p q A B $.

  verina71-all-substrings-graph-definition $a |- (
    VERINA71AllSubstringsGraph A B
  ) <-> (
    (
      A e. Word VERINA71Char
      /\
      B e. Word ( Word VERINA71Char )
    )
    /\
    E. p e. Word ( NN0 X. NN0 )
      (
        (
          ( # ` p ) = ( # ` B )
          /\
          A. q e. ( 0 ..^ ( # ` p ) )
            (
              (
                ( 1st ` ( p ` q ) ) < ( # ` A )
                /\
                (
                  1 <_ ( 2nd ` ( p ` q ) )
                  /\
                  ( 2nd ` ( p ` q ) ) <_ (
                    ( # ` A ) - ( 1st ` ( p ` q ) )
                  )
                )
              )
              /\
              (
                B ` q
              ) = (
                VERINA71Slice
                  A
                  ( 1st ` ( p ` q ) )
                  ( 2nd ` ( p ` q ) )
              )
            )
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` p ) )
            A. j e. ( 0 ..^ ( # ` p ) )
              (
                i < j
                ->
                (
                  (
                    ( 1st ` ( p ` i ) )
                    <
                    ( 1st ` ( p ` j ) )
                  )
                  \/
                  (
                    (
                      ( 1st ` ( p ` i ) )
                      =
                      ( 1st ` ( p ` j ) )
                    )
                    /\
                    (
                      ( 2nd ` ( p ` i ) )
                      <
                      ( 2nd ` ( p ` j ) )
                    )
                  )
                )
              )
          /\
          A. i e. ( 0 ..^ ( # ` A ) )
            A. l e. (
              1 ..^ ( ( ( # ` A ) - i ) + 1 )
            )
              E. q e. ( 0 ..^ ( # ` p ) )
                ( p ` q ) = <. i , l >.
        )
      )
  ) $.
$}

${
  $d y A $.

  verina71-all-substrings-definition $a |- (
    VERINA71AllSubstrings A
  ) = (
    iota_ y e. Word ( Word VERINA71Char )
      ( VERINA71AllSubstringsGraph A y )
  ) $.
$}

${
  $d i j p q A B C $.

  verina71-candidates-graph-definition $a |- (
    VERINA71CandidatesGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA71Char
        /\
        B e. NN0
      )
      /\
      C e. Word ( Word VERINA71Char )
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( # ` C )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              (
                p ` i
              ) < (
                # ` ( VERINA71AllSubstrings A )
              )
              /\
              (
                (
                  C ` i
                ) = (
                  ( VERINA71AllSubstrings A ) ` ( p ` i )
                )
                /\
                (
                  VERINA71CountOnes ( C ` i )
                ) = B
              )
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
          A. q e. (
            0 ..^ ( # ` ( VERINA71AllSubstrings A ) )
          )
            (
              (
                VERINA71CountOnes
                  ( ( VERINA71AllSubstrings A ) ` q )
              ) = B
              ->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = q
            )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina71-candidates-definition $a |- (
    VERINA71Candidates A B
  ) = (
    iota_ y e. Word ( Word VERINA71Char )
      ( VERINA71CandidatesGraph A B y )
  ) $.
$}

${
  $d i p A B $.

  verina71-lex-lt-definition $a |- (
    VERINA71LexLT A B
  ) <-> (
    (
      A e. Word VERINA71Char
      /\
      B e. Word VERINA71Char
    )
    /\
    (
      E. p e. (
        0 ..^ (
          VERINA71NatMin ( # ` A ) ( # ` B )
        )
      )
        (
          (
            A. i e. ( 0 ..^ p )
              ( A ` i ) = ( B ` i )
          )
          /\
          ( A ` p ) < ( B ` p )
        )
      \/
      (
        ( # ` A ) < ( # ` B )
        /\
        A. i e. ( 0 ..^ ( # ` A ) )
          ( A ` i ) = ( B ` i )
      )
    )
  ) $.
$}

verina71-lex-le-definition $a |- (
  VERINA71LexLE A B
) <-> (
  (
    (
      A e. Word VERINA71Char
      /\
      B e. Word VERINA71Char
    )
    /\
    -. ( VERINA71LexLT B A )
  )
) $.

verina71-is-lex-smaller-definition $a |- (
  VERINA71IsLexSmaller A B
) <-> (
  VERINA71LexLT
    ( VERINA71ListToString A )
    ( VERINA71ListToString B )
) $.

verina71-compare-definition $a |- (
  VERINA71Compare A B
) <-> (
  (
    A e. Word VERINA71Char
    /\
    B e. Word VERINA71Char
  )
  /\
  (
    ( # ` A ) < ( # ` B )
    \/
    (
      ( # ` A ) = ( # ` B )
      /\
      ( VERINA71IsLexSmaller A B )
    )
  )
) $.

verina71-none-definition $a |- VERINA71None = (/) $.

verina71-some-definition $a |- (
  VERINA71Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina71-option-string-definition $a |- VERINA71OptionString =
    { x |
      (
        x = VERINA71None
        \/
        E. y e. Word VERINA71Char
          x = ( VERINA71Some y )
      )
    } $.
$}

${
  $d i t A B $.

  verina71-best-graph-definition $a |- (
    VERINA71BestGraph A B
  ) <-> (
    (
      A e. Word ( Word VERINA71Char )
      /\
      B e. VERINA71OptionString
    )
    /\
    (
      (
        A = (/)
        /\
        B = VERINA71None
      )
      \/
      (
        A =/= (/)
        /\
        E. t e. Word ( Word VERINA71Char )
          (
            (
              (
                ( # ` t ) = ( # ` A )
                /\
                ( t ` 0 ) = ( A ` 0 )
              )
              /\
              A. i e. ( 1 ..^ ( # ` A ) )
                (
                  t ` i
                ) = if (
                  (
                    VERINA71Compare
                      ( A ` i )
                      ( t ` ( i - 1 ) )
                  ) ,
                  ( A ` i ) ,
                  ( t ` ( i - 1 ) )
                )
            )
            /\
            B = (
              VERINA71Some
                ( t ` ( ( # ` A ) - 1 ) )
            )
          )
      )
    )
  ) $.
$}

${
  $d y A $.

  verina71-best-definition $a |- (
    VERINA71Best A
  ) = (
    iota_ y e. VERINA71OptionString
      ( VERINA71BestGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina71-precondition-definition $a |- (
    VERINA71Pre A B
  ) <-> (
    (
      A e. Word VERINA71Char
      /\
      B e. NN0
    )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      (
        ( A ` i ) = ; 4 8
        \/
        ( A ` i ) = ; 4 9
      )
  ) $.
$}

verina71-program-definition $a |- (
  VERINA71ShortestBeautifulSubstring A B
) = if (
  (
    VERINA71Best
      ( VERINA71Candidates ( VERINA71Chars A ) B )
  ) = VERINA71None ,
  (/) ,
  (
    2nd ` (
      VERINA71Best
        ( VERINA71Candidates ( VERINA71Chars A ) B )
    )
  )
) $.

${
  $d i j l p q A B $.

  verina71-post-substrings-graph-definition $a |- (
    VERINA71PostSubstringsGraph A B
  ) <-> (
    (
      A e. Word VERINA71Char
      /\
      B e. Word ( Word VERINA71Char )
    )
    /\
    E. p e. Word ( NN0 X. NN0 )
      (
        (
          ( # ` p ) = ( # ` B )
          /\
          A. q e. ( 0 ..^ ( # ` p ) )
            (
              (
                ( 1st ` ( p ` q ) ) < ( # ` A )
                /\
                ( 2nd ` ( p ` q ) ) <_ (
                  ( # ` A ) - ( 1st ` ( p ` q ) )
                )
              )
              /\
              (
                B ` q
              ) = (
                VERINA71Slice
                  A
                  ( 1st ` ( p ` q ) )
                  ( 2nd ` ( p ` q ) )
              )
            )
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` p ) )
            A. j e. ( 0 ..^ ( # ` p ) )
              (
                i < j
                ->
                (
                  (
                    ( 1st ` ( p ` i ) )
                    <
                    ( 1st ` ( p ` j ) )
                  )
                  \/
                  (
                    (
                      ( 1st ` ( p ` i ) )
                      =
                      ( 1st ` ( p ` j ) )
                    )
                    /\
                    (
                      ( 2nd ` ( p ` i ) )
                      <
                      ( 2nd ` ( p ` j ) )
                    )
                  )
                )
              )
          /\
          A. i e. ( 0 ..^ ( # ` A ) )
            A. l e. (
              0 ..^ ( ( ( # ` A ) - i ) + 1 )
            )
              E. q e. ( 0 ..^ ( # ` p ) )
                ( p ` q ) = <. i , l >.
        )
      )
  ) $.
$}

${
  $d y A $.

  verina71-post-substrings-definition $a |- (
    VERINA71PostSubstrings A
  ) = (
    iota_ y e. Word ( Word VERINA71Char )
      ( VERINA71PostSubstringsGraph A y )
  ) $.
$}

${
  $d i j p q A B C $.

  verina71-targets-graph-definition $a |- (
    VERINA71TargetsGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA71Char
        /\
        B e. NN0
      )
      /\
      C e. Word ( Word VERINA71Char )
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( # ` C )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              (
                p ` i
              ) < (
                # ` ( VERINA71PostSubstrings ( VERINA71Chars A ) )
              )
              /\
              (
                (
                  VERINA71CountOnes
                    (
                      ( VERINA71PostSubstrings
                          ( VERINA71Chars A ) ) ` ( p ` i )
                    )
                ) = B
                /\
                (
                  (
                    VERINA71PostSubstrings
                      ( VERINA71Chars A )
                  ) ` ( p ` i )
                ) =/= (/)
              )
              /\
              (
                C ` i
              ) = (
                VERINA71StringMk
                  (
                    (
                      VERINA71PostSubstrings
                        ( VERINA71Chars A )
                    ) ` ( p ` i )
                  )
              )
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
          A. q e. (
            0 ..^ (
              # ` (
                VERINA71PostSubstrings ( VERINA71Chars A )
              )
            )
          )
            (
              (
                (
                  VERINA71CountOnes
                    (
                      ( VERINA71PostSubstrings
                          ( VERINA71Chars A ) ) ` q
                    )
                ) = B
                /\
                (
                  (
                    VERINA71PostSubstrings
                      ( VERINA71Chars A )
                  ) ` q
                ) =/= (/)
              )
              ->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = q
            )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina71-targets-definition $a |- (
    VERINA71Targets A B
  ) = (
    iota_ y e. Word ( Word VERINA71Char )
      ( VERINA71TargetsGraph A B y )
  ) $.
$}

${
  $d r A B C $.

  verina71-postcondition-definition $a |- (
    VERINA71Post A B C
  ) <-> (
    (
      (
        A e. Word VERINA71Char
        /\
        B e. NN0
      )
      /\
      C e. Word VERINA71Char
    )
    /\
    (
      (
        C = (/)
        /\
        ( VERINA71Targets A B ) = (/)
      )
      \/
      (
        C e. ran ( VERINA71Targets A B )
        /\
        A. r e. ran ( VERINA71Targets A B )
          (
            ( # ` C ) < ( # ` r )
            \/
            (
              ( # ` C ) = ( # ` r )
              /\
              ( VERINA71LexLE C r )
            )
          )
      )
    )
  ) $.
$}

${
  $d k s $.

  verina-advanced-71-shortest-beautiful-substring $a |-
    A. s e. Word VERINA71Char
      A. k e. NN0
        (
          ( VERINA71Pre s k )
          ->
          (
            VERINA71Post
              s
              k
              ( VERINA71ShortestBeautifulSubstring s k )
          )
        )
  $.
$}
