$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_46 (verina__metamath__verina_advanced_46), catalog title
  maxSubarraySum: the exact all-negative test and recursive Kadane-style scan
  compute the maximum sum of an empty or contiguous subarray of an arbitrary
  finite integer list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  i ..^ j is the half-open natural interval from i through j - 1.

  VERINA46IsAllNegative is exactly the source Boolean recursion: it is true
  precisely when every entry is strictly negative, including vacuous truth
  on the empty list. VERINA46FindMaxProductGraph records the exact finite
  execution of findMaxProduct. On an empty helper input it returns currMax.
  On a nonempty input, c and g record currSum and currMax: the first entries
  are the supplied accumulators, every later entry performs the source update
    newSum = max y (currSum + y)
    newMax = max currMax newSum,
  and the final max with the last list entry is the singleton branch.
  VERINA46FindMaxProduct selects the unique result of this graph.

  VERINA46ToNat is Lean Int.toNat. VERINA46MaxSubarraySum preserves the exact
  handleList branches: the empty and all-negative cases return zero; otherwise
  both initial accumulators are max 0 head, the helper runs on the original
  nonempty list, and its result is converted to Nat and then back to Int.

  VERINA46PrefixGraph gives the unique integer prefix sums beginning at zero.
  VERINA46SubarraySumsGraph reproduces the two List.range calls in the
  postcondition. Its pair word contains, in increasing start and then length
  order, every pair with start at most the input length and length at most the
  remaining suffix length. Thus it retains all duplicate sums and all empty
  subarray occurrences, including the one at the end of the list.

  VERINA46Pre is the source True precondition together with the List Int input
  type. VERINA46Post is exactly List.contains followed by List.all on the
  independently enumerated subarray sums. The proof-valued precondition
  argument is computationally and propositionally unused and is omitted from
  the target function and predicate. The final $a declaration is the source
  correctness proposition. Every earlier $a is syntax or a faithful
  definition, and this database has no $p declaration.
$)

$c
  VERINA46IntMax VERINA46IsAllNegative
  VERINA46FindMaxProductGraph VERINA46FindMaxProduct
  VERINA46ToNat VERINA46Pre VERINA46MaxSubarraySum
  VERINA46PrefixGraph VERINA46Prefix
  VERINA46SubarraySumsGraph VERINA46SubarraySums
  VERINA46Post
$.

verina46-int-max-syntax
  $a class ( VERINA46IntMax A B ) $.
verina46-is-all-negative-syntax
  $a class ( VERINA46IsAllNegative A ) $.
verina46-find-max-product-graph-syntax
  $a wff ( VERINA46FindMaxProductGraph A B C D ) $.
verina46-find-max-product-syntax
  $a class ( VERINA46FindMaxProduct A B C ) $.
verina46-to-nat-syntax
  $a class ( VERINA46ToNat A ) $.
verina46-precondition-syntax
  $a wff ( VERINA46Pre A ) $.
verina46-max-subarray-sum-syntax
  $a class ( VERINA46MaxSubarraySum A ) $.
verina46-prefix-graph-syntax
  $a wff ( VERINA46PrefixGraph A B ) $.
verina46-prefix-syntax
  $a class ( VERINA46Prefix A ) $.
verina46-subarray-sums-graph-syntax
  $a wff ( VERINA46SubarraySumsGraph A B ) $.
verina46-subarray-sums-syntax
  $a class ( VERINA46SubarraySums A ) $.
verina46-postcondition-syntax
  $a wff ( VERINA46Post A B ) $.

verina46-int-max-definition $a |- (
  VERINA46IntMax A B
) = if (
  A < B ,
  B ,
  A
) $.

${
  $d k A $.

  verina46-is-all-negative-definition $a |- (
    VERINA46IsAllNegative A
  ) = if (
    A. k e. ( 0 ..^ ( # ` A ) )
      ( A ` k ) < 0 ,
    1 ,
    0
  ) $.
$}

${
  $d k c g A B C D $.

  verina46-find-max-product-graph-definition $a |- (
    VERINA46FindMaxProductGraph A B C D
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      (
        C e. ZZ
        /\
        D e. ZZ
      )
    )
    /\
    (
      (
        A = (/)
        /\
        D = B
      )
      \/
      (
        0 < ( # ` A )
        /\
        E. c e. Word ZZ
          E. g e. Word ZZ
            (
              (
                (
                  ( # ` c ) = ( # ` A )
                  /\
                  ( # ` g ) = ( # ` A )
                )
                /\
                (
                  ( c ` 0 ) = C
                  /\
                  ( g ` 0 ) = B
                )
              )
              /\
              (
                A. k e. ( 1 ..^ ( # ` A ) )
                  (
                    (
                      c ` k
                    ) = (
                      VERINA46IntMax
                        ( A ` k )
                        ( ( c ` ( k - 1 ) ) + ( A ` k ) )
                    )
                    /\
                    (
                      g ` k
                    ) = (
                      VERINA46IntMax
                        ( g ` ( k - 1 ) )
                        ( c ` k )
                    )
                  )
                /\
                D = (
                  VERINA46IntMax
                    ( g ` ( ( # ` A ) - 1 ) )
                    ( A ` ( ( # ` A ) - 1 ) )
                )
              )
            )
      )
    )
  ) $.
$}

${
  $d y A B C $.

  verina46-find-max-product-definition $a |- (
    VERINA46FindMaxProduct A B C
  ) = (
    iota_ y e. ZZ
      ( VERINA46FindMaxProductGraph A B C y )
  ) $.
$}

verina46-to-nat-definition $a |- (
  VERINA46ToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

verina46-precondition-definition $a |- (
  VERINA46Pre A
) <-> (
  A e. Word ZZ
) $.

verina46-max-subarray-sum-definition $a |- (
  VERINA46MaxSubarraySum A
) = if (
  ( # ` A ) = 0 ,
  0 ,
  if (
    ( VERINA46IsAllNegative A ) = 1 ,
    0 ,
    VERINA46ToNat
      (
        VERINA46FindMaxProduct
          A
          ( VERINA46IntMax 0 ( A ` 0 ) )
          ( VERINA46IntMax 0 ( A ` 0 ) )
      )
  )
) $.

${
  $d i A B $.

  verina46-prefix-graph-definition $a |- (
    VERINA46PrefixGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      (
        ( # ` B ) = ( ( # ` A ) + 1 )
        /\
        ( B ` 0 ) = 0
      )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` ( i + 1 )
        ) = (
          ( B ` i ) + ( A ` i )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina46-prefix-definition $a |- (
    VERINA46Prefix A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA46PrefixGraph A y )
  ) $.
$}

${
  $d i j l p q s A B $.

  verina46-subarray-sums-graph-definition $a |- (
    VERINA46SubarraySumsGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
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
                (
                  VERINA46Prefix A
                ) ` (
                  ( 1st ` ( p ` i ) ) +
                  ( 2nd ` ( p ` i ) )
                )
                -
                (
                  VERINA46Prefix A
                ) ` (
                  1st ` ( p ` i )
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
                (
                  (
                    1st ` ( p ` i )
                  ) < (
                    1st ` ( p ` j )
                  )
                  \/
                  (
                    (
                      1st ` ( p ` i )
                    ) = (
                      1st ` ( p ` j )
                    )
                    /\
                    (
                      2nd ` ( p ` i )
                    ) < (
                      2nd ` ( p ` j )
                    )
                  )
                )
              )
          /\
          A. s e. NN0
            A. l e. NN0
              (
                (
                  s <_ ( # ` A )
                  /\
                  l <_ ( ( # ` A ) - s )
                )
                ->
                E. q e. ( 0 ..^ ( # ` p ) )
                  ( p ` q ) = <. s , l >.
              )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina46-subarray-sums-definition $a |- (
    VERINA46SubarraySums A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA46SubarraySumsGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina46-postcondition-definition $a |- (
    VERINA46Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      B e. ran ( VERINA46SubarraySums A )
      /\
      A. i e. (
        0 ..^ ( # ` ( VERINA46SubarraySums A ) )
      )
        (
          ( VERINA46SubarraySums A ) ` i
        ) <_ B
    )
  ) $.
$}

verina-advanced-46-max-subarray-sum
  $a |- A. w e. Word ZZ
    (
      ( VERINA46Pre w )
      ->
      (
        VERINA46Post
          w
          ( VERINA46MaxSubarraySum w )
      )
    )
  $.
