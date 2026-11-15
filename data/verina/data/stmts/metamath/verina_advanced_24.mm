$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_24 (verina__metamath__verina_advanced_24), catalog title
  lengthOfLIS: an exact executable tail-replacement fold computes an integer
  length, with the contract that it is the maximum length of a strictly
  increasing subsequence of the input integer list. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its natural-number
  length, w ` k is zero-based lookup, and 0 ..^ ( # ` w ) is its complete
  index set. Natural lengths embed canonically in ZZ, matching Lean's
  coercion from List.length to Int.

  VERINA24ReplaceGraph is the exact source replace recursion, including its
  arbitrary list and accumulator arguments and the integer x captured by the
  enclosing helper. Its position p is the first list entry at least x, or the
  list length if none exists. The output is the reversed initial accumulator,
  the traversed prefix, x, and then the suffix after the replaced entry; at
  the end of the list, x is appended instead. VERINA24Replace selects this
  unique output, and VERINA24LisHelper calls it with the empty accumulator.

  VERINA24FinalDPGraph threads VERINA24LisHelper through nums from left to
  right, exactly reproducing List.foldl. VERINA24LengthOfLIS is the integer
  coercion of the final word length, so the implementation remains connected
  explicitly to the final correctness assertion.

  VERINA24StrictlyIncreasing is the source Boolean adjacency recursion.
  VERINA24BitSet and VERINA24MaskWordGraph enumerate each subsequence by the
  binary mask whose most-significant input-position bit corresponds to the
  list head. Numeric mask order therefore gives exactly
  rest ++ rest.map (fun r => x :: r) at every recursive step, preserving
  order and duplicate occurrences. VERINA24Subsequences selects that exact
  word of words. VERINA24AllIncreasingGraph is the exact stable filter by
  VERINA24StrictlyIncreasing, and VERINA24AllIncreasing selects its unique
  result.

  VERINA24Pre is the source True precondition together with the List Int
  input type. VERINA24Post reproduces List.any for a subsequence whose length
  equals the result and List.all asserting that every increasing subsequence
  length is at most the result. The proof-valued precondition argument is
  computationally and propositionally unused and is omitted from the target
  function and predicate. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and this
  database has no $p declaration.
$)

$c
  VERINA24ReplaceGraph VERINA24Replace VERINA24LisHelper
  VERINA24FinalDPGraph VERINA24FinalDP
  VERINA24Pre VERINA24LengthOfLIS
  VERINA24StrictlyIncreasing
  VERINA24BitSet VERINA24MaskWordGraph
  VERINA24SubsequencesGraph VERINA24Subsequences
  VERINA24AllIncreasingGraph VERINA24AllIncreasing
  VERINA24Post
$.

verina24-replace-graph-syntax
  $a wff ( VERINA24ReplaceGraph A B C D ) $.
verina24-replace-syntax
  $a class ( VERINA24Replace A B C ) $.
verina24-lis-helper-syntax
  $a class ( VERINA24LisHelper A B ) $.
verina24-final-dp-graph-syntax
  $a wff ( VERINA24FinalDPGraph A B ) $.
verina24-final-dp-syntax
  $a class ( VERINA24FinalDP A ) $.
verina24-precondition-syntax
  $a wff ( VERINA24Pre A ) $.
verina24-length-of-lis-syntax
  $a class ( VERINA24LengthOfLIS A ) $.
verina24-strictly-increasing-syntax
  $a wff ( VERINA24StrictlyIncreasing A ) $.
verina24-bit-set-syntax
  $a wff ( VERINA24BitSet A B ) $.
verina24-mask-word-graph-syntax
  $a wff ( VERINA24MaskWordGraph A B C ) $.
verina24-subsequences-graph-syntax
  $a wff ( VERINA24SubsequencesGraph A B ) $.
verina24-subsequences-syntax
  $a class ( VERINA24Subsequences A ) $.
verina24-all-increasing-graph-syntax
  $a wff ( VERINA24AllIncreasingGraph A B ) $.
verina24-all-increasing-syntax
  $a class ( VERINA24AllIncreasing A ) $.
verina24-postcondition-syntax
  $a wff ( VERINA24Post A B ) $.

${
  $d j p A B C D $.

  verina24-replace-graph-definition $a |- (
    VERINA24ReplaceGraph A B C D
  ) <-> (
    (
      (
        A e. ZZ
        /\
        B e. Word ZZ
      )
      /\
      (
        C e. Word ZZ
        /\
        D e. Word ZZ
      )
    )
    /\
    E. p e. NN0
      (
        p <_ ( # ` B )
        /\
        (
          (
            A. j e. ( 0 ..^ p )
              -. A <_ ( B ` j )
            /\
            (
              p < ( # ` B )
              ->
              A <_ ( B ` p )
            )
          )
          /\
          (
            ( # ` D ) = if (
              p < ( # ` B ) ,
              ( ( # ` C ) + ( # ` B ) ) ,
              ( ( ( # ` C ) + ( # ` B ) ) + 1 )
            )
            /\
            (
              A. j e. ( 0 ..^ ( # ` C ) )
                (
                  D ` j
                ) = (
                  C ` ( ( ( # ` C ) - 1 ) - j )
                )
              /\
              (
                A. j e. (
                  ( # ` C ) ..^ ( ( # ` C ) + p )
                )
                  (
                    D ` j
                  ) = (
                    B ` ( j - ( # ` C ) )
                  )
                /\
                (
                  (
                    D ` ( ( # ` C ) + p )
                  ) = A
                  /\
                  A. j e. ( ( p + 1 ) ..^ ( # ` B ) )
                    (
                      D ` ( ( # ` C ) + j )
                    ) = (
                      B ` j
                    )
                )
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verina24-replace-definition $a |- (
    VERINA24Replace A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINA24ReplaceGraph A B C y )
  ) $.
$}

verina24-lis-helper-definition $a |- (
  VERINA24LisHelper A B
) = (
  VERINA24Replace B A (/)
) $.

${
  $d k t A B $.

  verina24-final-dp-graph-definition $a |- (
    VERINA24FinalDPGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = (/)
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              t ` ( k + 1 )
            ) = (
              VERINA24LisHelper
                ( t ` k )
                ( A ` k )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina24-final-dp-definition $a |- (
    VERINA24FinalDP A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA24FinalDPGraph A y )
  ) $.
$}

verina24-precondition-definition $a |- (
  VERINA24Pre A
) <-> (
  A e. Word ZZ
) $.

verina24-length-of-lis-definition $a |- (
  VERINA24LengthOfLIS A
) = (
  # ` ( VERINA24FinalDP A )
) $.

${
  $d i A $.

  verina24-strictly-increasing-definition $a |- (
    VERINA24StrictlyIncreasing A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( ( # ` A ) - 1 ) )
        ( A ` i ) < ( A ` ( i + 1 ) )
    )
  ) $.
$}

verina24-bit-set-definition $a |- (
  VERINA24BitSet A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2
  ) = 1
) $.

${
  $d i j k p A B C $.

  verina24-mask-word-graph-definition $a |- (
    VERINA24MaskWordGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ( 0 ..^ ( 2 ^ ( # ` A ) ) )
      )
      /\
      C e. Word ZZ
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( # ` C )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              ( p ` i ) < ( # ` A )
              /\
              ( C ` i ) = ( A ` ( p ` i ) )
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
                VERINA24BitSet
                  B
                  ( ( ( # ` A ) - 1 ) - k )
              )
              <->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = k
            )
        )
      )
  ) $.
$}

${
  $d r A B $.

  verina24-subsequences-graph-definition $a |- (
    VERINA24SubsequencesGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
    )
    /\
    (
      ( # ` B ) = ( 2 ^ ( # ` A ) )
      /\
      A. r e. ( 0 ..^ ( # ` B ) )
        (
          VERINA24MaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina24-subsequences-definition $a |- (
    VERINA24Subsequences A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA24SubsequencesGraph A y )
  ) $.
$}

${
  $d i j k p A B $.

  verina24-all-increasing-graph-definition $a |- (
    VERINA24AllIncreasingGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( # ` B )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              (
                ( p ` i )
                <
                ( # ` ( VERINA24Subsequences A ) )
              )
              /\
              (
                VERINA24StrictlyIncreasing
                  (
                    ( VERINA24Subsequences A )
                    ` ( p ` i )
                  )
                /\
                (
                  B ` i
                ) = (
                  ( VERINA24Subsequences A )
                  ` ( p ` i )
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
          A. k e. (
            0 ..^ ( # ` ( VERINA24Subsequences A ) )
          )
            (
              (
                VERINA24StrictlyIncreasing
                  ( ( VERINA24Subsequences A ) ` k )
              )
              ->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = k
            )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina24-all-increasing-definition $a |- (
    VERINA24AllIncreasing A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA24AllIncreasingGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina24-postcondition-definition $a |- (
    VERINA24Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      E. i e. (
        0 ..^ ( # ` ( VERINA24AllIncreasing A ) )
      )
        (
          # ` ( ( VERINA24AllIncreasing A ) ` i )
        ) = B
      /\
      A. i e. (
        0 ..^ ( # ` ( VERINA24AllIncreasing A ) )
      )
        (
          # ` ( ( VERINA24AllIncreasing A ) ` i )
        ) <_ B
    )
  ) $.
$}

verina-advanced-24-length-of-lis $a |- A. w e. Word ZZ
  (
    ( VERINA24Pre w )
    ->
    (
      VERINA24Post
        w
        ( VERINA24LengthOfLIS w )
    )
  )
$.
