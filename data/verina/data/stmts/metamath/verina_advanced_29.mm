$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_29 (verina__metamath__verina_advanced_29), catalog title
  longestGoodSubarray: the exact bounded sliding-window program returns the
  maximum length of a contiguous subarray whose element frequencies are at
  most the positive natural bound. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` i is zero-based lookup, and i ..^ j is the
  half-open natural interval from i through j - 1.

  VERINA29WindowCount is the multiplicity of a value in a half-open slice,
  and VERINA29WindowGood says every entry in that slice has multiplicity at
  most k. The source HashMap is represented extensionally by these counts:
  after insertion at right and each removal at left, its positive entries are
  exactly the multiplicities in nums[left .. right + 1]. HashMap bucket
  layout and capacity are unobservable.

  VERINA29StepLeft gives the exact result of the source's bounded inner loop.
  It chooses the least index at or after the previous left endpoint for which
  the current window is good. Because k is positive, the singleton ending at
  right is good, so this endpoint is reached within the source bound of
  nums.length iterations. VERINA29RunGraph threads these left endpoints and
  maxLen values through every right endpoint and applies the same natural
  subtraction, addition, and maximum update. VERINA29LongestGoodSubarray
  selects the unique final value, independently of the postcondition.

  VERINA29Extract is the exact drop-then-take operation on every valid range.
  VERINA29Subarrays enumerates the source pair order: starts from zero through
  nums.length, and for each start lengths from zero through the remaining
  length. VERINA29FreqWord maps every element occurrence to its count in that
  extracted word. VERINA29SubarrayFreqs performs that map over the complete
  subarray word. VERINA29ValidSubarrays is the exact stable filter retaining
  precisely the frequency words whose entries are all at most k, including
  every duplicate occurrence and every empty subarray occurrence.

  VERINA29Pre is the positive-k precondition. VERINA29Post reproduces the
  source empty-input branch and, for nonempty input, its List.any equality of
  a retained word length with the result and List.all upper-bound check. The
  proof-valued precondition argument is computationally and propositionally
  unused and is omitted from the target function and postcondition predicate.
  The final $a declaration is the source correctness proposition. Every
  earlier $a is syntax or a faithful definition, and this database has no
  $p declaration.
$)

$c
  VERINA29WindowCount VERINA29WindowGood
  VERINA29StepLeft VERINA29RunGraph VERINA29LongestGoodSubarray
  VERINA29ExtractGraph VERINA29Extract
  VERINA29SubarraysGraph VERINA29Subarrays
  VERINA29Count VERINA29FreqWordGraph VERINA29FreqWord
  VERINA29SubarrayFreqsGraph VERINA29SubarrayFreqs
  VERINA29AllAtMost
  VERINA29ValidSubarraysGraph VERINA29ValidSubarrays
  VERINA29Pre VERINA29Post
$.

verina29-window-count-syntax
  $a class ( VERINA29WindowCount A B C D ) $.
verina29-window-good-syntax
  $a wff ( VERINA29WindowGood A B C D ) $.
verina29-step-left-syntax
  $a wff ( VERINA29StepLeft A B C D E ) $.
verina29-run-graph-syntax
  $a wff ( VERINA29RunGraph A B C ) $.
verina29-longest-good-subarray-syntax
  $a class ( VERINA29LongestGoodSubarray A B ) $.
verina29-extract-graph-syntax
  $a wff ( VERINA29ExtractGraph A B C D ) $.
verina29-extract-syntax
  $a class ( VERINA29Extract A B C ) $.
verina29-subarrays-graph-syntax
  $a wff ( VERINA29SubarraysGraph A B ) $.
verina29-subarrays-syntax
  $a class ( VERINA29Subarrays A ) $.
verina29-count-syntax
  $a class ( VERINA29Count A B ) $.
verina29-freq-word-graph-syntax
  $a wff ( VERINA29FreqWordGraph A B ) $.
verina29-freq-word-syntax
  $a class ( VERINA29FreqWord A ) $.
verina29-subarray-freqs-graph-syntax
  $a wff ( VERINA29SubarrayFreqsGraph A B ) $.
verina29-subarray-freqs-syntax
  $a class ( VERINA29SubarrayFreqs A ) $.
verina29-all-at-most-syntax
  $a wff ( VERINA29AllAtMost A B ) $.
verina29-valid-subarrays-graph-syntax
  $a wff ( VERINA29ValidSubarraysGraph A B C ) $.
verina29-valid-subarrays-syntax
  $a class ( VERINA29ValidSubarrays A B ) $.
verina29-precondition-syntax
  $a wff ( VERINA29Pre A B ) $.
verina29-postcondition-syntax
  $a wff ( VERINA29Post A B C ) $.

${
  $d i A B C D $.

  verina29-window-count-definition $a |- (
    VERINA29WindowCount A B C D
  ) = (
    # ` {
      i e. ( B ..^ C )
      |
      ( A ` i ) = D
    }
  ) $.
$}

${
  $d i A B C D $.

  verina29-window-good-definition $a |- (
    VERINA29WindowGood A B C D
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. NN0
      )
    )
    /\
    (
      (
        B <_ C
        /\
        C <_ ( # ` A )
      )
      /\
      A. i e. ( B ..^ C )
        (
          VERINA29WindowCount A B C ( A ` i )
        ) <_ D
    )
  ) $.
$}

${
  $d q A B C D E $.

  verina29-step-left-definition $a |- (
    VERINA29StepLeft A B C D E
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. NN0
      )
    )
    /\
    (
      E e. NN0
      /\
      (
        (
          0 < B
          /\
          (
            C <_ E
            /\
            E <_ D
          )
        )
        /\
        (
          D < ( # ` A )
          /\
          (
            ( VERINA29WindowGood A E ( D + 1 ) B )
            /\
            A. q e. NN0
              (
                (
                  C <_ q
                  /\
                  q < E
                )
                ->
                -. ( VERINA29WindowGood A q ( D + 1 ) B )
              )
          )
        )
      )
    )
  ) $.
$}

${
  $d r l m A B C $.

  verina29-run-graph-definition $a |- (
    VERINA29RunGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      (
        0 < B
        /\
        C e. NN0
      )
    )
    /\
    E. l e. Word NN0
      E. m e. Word NN0
        (
          (
            (
              ( # ` l ) = ( ( # ` A ) + 1 )
              /\
              ( # ` m ) = ( ( # ` A ) + 1 )
            )
            /\
            (
              ( l ` 0 ) = 0
              /\
              ( m ` 0 ) = 0
            )
          )
          /\
          (
            A. r e. ( 0 ..^ ( # ` A ) )
              (
                (
                  VERINA29StepLeft
                    A B ( l ` r ) r ( l ` ( r + 1 ) )
                )
                /\
                (
                  m ` ( r + 1 )
                ) = if (
                  ( m ` r ) < (
                    ( r - ( l ` ( r + 1 ) ) ) + 1
                  ) ,
                  ( ( r - ( l ` ( r + 1 ) ) ) + 1 ) ,
                  ( m ` r )
                )
              )
            /\
            C = ( m ` ( # ` A ) )
          )
        )
  ) $.
$}

${
  $d y A B $.

  verina29-longest-good-subarray-definition $a |- (
    VERINA29LongestGoodSubarray A B
  ) = (
    iota_ y e. NN0
      ( VERINA29RunGraph A B y )
  ) $.
$}

${
  $d i A B C D $.

  verina29-extract-graph-definition $a |- (
    VERINA29ExtractGraph A B C D
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. Word NN0
      )
    )
    /\
    (
      (
        B <_ ( # ` A )
        /\
        C <_ ( ( # ` A ) - B )
      )
      /\
      (
        ( # ` D ) = C
        /\
        A. i e. ( 0 ..^ C )
          ( D ` i ) = ( A ` ( B + i ) )
      )
    )
  ) $.
$}

${
  $d y A B C $.

  verina29-extract-definition $a |- (
    VERINA29Extract A B C
  ) = (
    iota_ y e. Word NN0
      ( VERINA29ExtractGraph A B C y )
  ) $.
$}

${
  $d i j q r p A B $.

  verina29-subarrays-graph-definition $a |- (
    VERINA29SubarraysGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. Word ( Word NN0 )
    )
    /\
    E. p e. Word ( NN0 X. NN0 )
      (
        (
          ( # ` p ) = ( # ` B )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              (
                ( 1st ` ( p ` i ) ) <_ ( # ` A )
                /\
                ( 2nd ` ( p ` i ) ) <_ (
                  ( # ` A ) - ( 1st ` ( p ` i ) )
                )
              )
              /\
              (
                B ` i
              ) = (
                VERINA29Extract
                  A
                  ( 1st ` ( p ` i ) )
                  ( 2nd ` ( p ` i ) )
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
          A. q e. NN0
            A. r e. NN0
              (
                (
                  q <_ ( # ` A )
                  /\
                  r <_ ( ( # ` A ) - q )
                )
                ->
                E. i e. ( 0 ..^ ( # ` p ) )
                  ( p ` i ) = <. q , r >.
              )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina29-subarrays-definition $a |- (
    VERINA29Subarrays A
  ) = (
    iota_ y e. Word ( Word NN0 )
      ( VERINA29SubarraysGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina29-count-definition $a |- (
    VERINA29Count A B
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` B ) )
      |
      ( B ` i ) = A
    }
  ) $.
$}

${
  $d i A B $.

  verina29-freq-word-graph-definition $a |- (
    VERINA29FreqWordGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. Word NN0
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` i
        ) = (
          VERINA29Count ( A ` i ) A
        )
    )
  ) $.
$}

${
  $d y A $.

  verina29-freq-word-definition $a |- (
    VERINA29FreqWord A
  ) = (
    iota_ y e. Word NN0
      ( VERINA29FreqWordGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina29-subarray-freqs-graph-definition $a |- (
    VERINA29SubarrayFreqsGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. Word ( Word NN0 )
    )
    /\
    (
      ( # ` B ) = ( # ` ( VERINA29Subarrays A ) )
      /\
      A. i e. ( 0 ..^ ( # ` B ) )
        (
          B ` i
        ) = (
          VERINA29FreqWord
            ( ( VERINA29Subarrays A ) ` i )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina29-subarray-freqs-definition $a |- (
    VERINA29SubarrayFreqs A
  ) = (
    iota_ y e. Word ( Word NN0 )
      ( VERINA29SubarrayFreqsGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina29-all-at-most-definition $a |- (
    VERINA29AllAtMost A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      ( A ` i ) <_ B
  ) $.
$}

${
  $d i j p A B C $.

  verina29-valid-subarrays-graph-definition $a |- (
    VERINA29ValidSubarraysGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. Word ( Word NN0 )
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
                ( p ` i ) < (
                  # ` ( VERINA29SubarrayFreqs A )
                )
                /\
                (
                  VERINA29AllAtMost
                    ( ( VERINA29SubarrayFreqs A ) ` ( p ` i ) )
                    B
                )
              )
              /\
              (
                C ` i
              ) = (
                ( VERINA29SubarrayFreqs A ) ` ( p ` i )
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
          A. j e. (
            0 ..^ ( # ` ( VERINA29SubarrayFreqs A ) )
          )
            (
              (
                VERINA29AllAtMost
                  ( ( VERINA29SubarrayFreqs A ) ` j )
                  B
              )
              ->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = j
            )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina29-valid-subarrays-definition $a |- (
    VERINA29ValidSubarrays A B
  ) = (
    iota_ y e. Word ( Word NN0 )
      ( VERINA29ValidSubarraysGraph A B y )
  ) $.
$}

verina29-precondition-definition $a |- (
  VERINA29Pre A B
) <-> (
  (
    A e. Word NN0
    /\
    (
      B e. NN0
      /\
      0 < B
    )
  )
) $.

${
  $d i A B C $.

  verina29-postcondition-definition $a |- (
    VERINA29Post A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. NN0
    )
    /\
    (
      (
        A = (/)
        /\
        C = 0
      )
      \/
      (
        A =/= (/)
        /\
        (
          E. i e. (
            0 ..^ ( # ` ( VERINA29ValidSubarrays A B ) )
          )
            (
              # ` ( ( VERINA29ValidSubarrays A B ) ` i )
            ) = C
          /\
          A. i e. (
            0 ..^ ( # ` ( VERINA29ValidSubarrays A B ) )
          )
            (
              # ` ( ( VERINA29ValidSubarrays A B ) ` i )
            ) <_ C
        )
      )
    )
  ) $.
$}

verina-advanced-29-longest-good-subarray
  $a |- A. w e. Word NN0
    A. k e. NN0
      (
        ( VERINA29Pre w k )
        ->
        (
          VERINA29Post
            w
            k
            ( VERINA29LongestGoodSubarray w k )
        )
      )
  $.
