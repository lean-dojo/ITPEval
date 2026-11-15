$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_44 (verina__metamath__verina_advanced_44), catalog title
  maxSubarraySumDivisibleByK: the exact prefix-sum and nested-loop program
  computes a defaulted maximum sum of contiguous subarrays with eligible
  lengths, together with its independently enumerated divisibility
  postcondition for arbitrary finite integer arrays and integer k. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  i ..^ j is the half-open natural interval from i through j - 1.

  VERINA44PrefixGraph is the exact trace produced by Array.mkArray followed
  by the source loop of set! updates: it starts at integer zero and records
  every successive array prefix sum. VERINA44IntRemainderZero captures
  ((len : Int) % k = 0) exactly on natural len, including Lean's behavior
  len % 0 = len.

  VERINA44ImplSumsGraph enumerates precisely the successful iterations of the
  implementation's outer List.range (n + 1) and inner
  List.range (n - len + 1), in length-major and then start-major order. Each
  output is the same difference of prefix sums. VERINA44None,
  VERINA44Some, and VERINA44OptionInt encode Option Int.
  VERINA44BestOptionGraph is the exact mutable best trace: it remains none on
  an empty candidate word, starts with the first sum otherwise, and applies
  integer max left-to-right. VERINA44OptionGetD performs the final match with
  default zero. VERINA44MaxSubarraySumDivisibleByK also preserves the source
  early return when the array is empty or k is zero.

  VERINA44ToNat is Lean Int.toNat. VERINA44PostLengthEligible therefore
  reproduces the postcondition's
    subarray.size % k.toNat = 0 && subarray.size > 0,
  including the absence of eligible positive lengths when k is nonpositive.
  VERINA44Extract is Array.extract on the in-range endpoints generated here.
  VERINA44PostSubarraysGraph preserves the source flatMap order: starts are
  zero through n - 1, and lengths for each start are zero through n - start.
  VERINA44DivisibleSubarraysGraph is the exact stable filter, retaining
  duplicate occurrences. VERINA44Sum is List.sum from integer zero, and
  VERINA44SubarraySumsGraph maps it over the filtered word.

  VERINA44Pre is the source positive-k precondition. The official final Lean
  proposition does not assume that precondition, so the final $a likewise
  quantifies unconditionally over every integer k. VERINA44Post preserves
  both source implications: an empty sum word forces result zero, while a
  nonempty sum word requires the result to occur and to bound every sum.
  Every earlier $a is syntax or a faithful definition, and this root
  statement file introduces no $p declaration.
$)

$c
  VERINA44PrefixGraph VERINA44Prefix
  VERINA44IntRemainderZero
  VERINA44ImplSumsGraph VERINA44ImplSums
  VERINA44None VERINA44Some VERINA44OptionInt
  VERINA44BestOptionGraph VERINA44BestOption VERINA44OptionGetD
  VERINA44Pre VERINA44MaxSubarraySumDivisibleByK
  VERINA44ToNat VERINA44PostLengthEligible
  VERINA44ExtractGraph VERINA44Extract
  VERINA44PostSubarraysGraph VERINA44PostSubarrays
  VERINA44DivisibleSubarraysGraph VERINA44DivisibleSubarrays
  VERINA44Sum
  VERINA44SubarraySumsGraph VERINA44SubarraySums
  VERINA44Post
$.

verina44-prefix-graph-syntax
  $a wff ( VERINA44PrefixGraph A B ) $.
verina44-prefix-syntax
  $a class ( VERINA44Prefix A ) $.
verina44-int-remainder-zero-syntax
  $a wff ( VERINA44IntRemainderZero A B ) $.
verina44-impl-sums-graph-syntax
  $a wff ( VERINA44ImplSumsGraph A B C ) $.
verina44-impl-sums-syntax
  $a class ( VERINA44ImplSums A B ) $.
verina44-none-syntax
  $a class VERINA44None $.
verina44-some-syntax
  $a class ( VERINA44Some A ) $.
verina44-option-int-syntax
  $a class VERINA44OptionInt $.
verina44-best-option-graph-syntax
  $a wff ( VERINA44BestOptionGraph A B ) $.
verina44-best-option-syntax
  $a class ( VERINA44BestOption A ) $.
verina44-option-get-d-syntax
  $a class ( VERINA44OptionGetD A ) $.
verina44-precondition-syntax
  $a wff ( VERINA44Pre A B ) $.
verina44-max-subarray-sum-divisible-by-k-syntax
  $a class ( VERINA44MaxSubarraySumDivisibleByK A B ) $.
verina44-to-nat-syntax
  $a class ( VERINA44ToNat A ) $.
verina44-post-length-eligible-syntax
  $a wff ( VERINA44PostLengthEligible A B ) $.
verina44-extract-graph-syntax
  $a wff ( VERINA44ExtractGraph A B C D ) $.
verina44-extract-syntax
  $a class ( VERINA44Extract A B C ) $.
verina44-post-subarrays-graph-syntax
  $a wff ( VERINA44PostSubarraysGraph A B ) $.
verina44-post-subarrays-syntax
  $a class ( VERINA44PostSubarrays A ) $.
verina44-divisible-subarrays-graph-syntax
  $a wff ( VERINA44DivisibleSubarraysGraph A B C ) $.
verina44-divisible-subarrays-syntax
  $a class ( VERINA44DivisibleSubarrays A B ) $.
verina44-sum-syntax
  $a class ( VERINA44Sum A ) $.
verina44-subarray-sums-graph-syntax
  $a wff ( VERINA44SubarraySumsGraph A B C ) $.
verina44-subarray-sums-syntax
  $a class ( VERINA44SubarraySums A B ) $.
verina44-postcondition-syntax
  $a wff ( VERINA44Post A B C ) $.

${
  $d i A B $.

  verina44-prefix-graph-definition $a |- (
    VERINA44PrefixGraph A B
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

  verina44-prefix-definition $a |- (
    VERINA44Prefix A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA44PrefixGraph A y )
  ) $.
$}

${
  $d q A B $.

  verina44-int-remainder-zero-definition $a |- (
    VERINA44IntRemainderZero A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. ZZ
    )
    /\
    E. q e. ZZ
      A = ( B x. q )
  ) $.
$}

${
  $d i j l p q s A B C $.

  verina44-impl-sums-graph-definition $a |- (
    VERINA44ImplSumsGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    E. p e. Word ( NN0 X. NN0 )
      (
        (
          ( # ` p ) = ( # ` C )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              (
                (
                  ( 1st ` ( p ` i ) ) <_ ( # ` A )
                  /\
                  (
                    VERINA44IntRemainderZero
                      ( 1st ` ( p ` i ) )
                      B
                  )
                )
                /\
                (
                  0 < ( 1st ` ( p ` i ) )
                  /\
                  ( 2nd ` ( p ` i ) ) <_ (
                    ( # ` A ) - ( 1st ` ( p ` i ) )
                  )
                )
              )
              /\
              (
                C ` i
              ) = (
                (
                  VERINA44Prefix A
                ) ` (
                  ( 2nd ` ( p ` i ) ) +
                  ( 1st ` ( p ` i ) )
                )
                -
                (
                  VERINA44Prefix A
                ) ` (
                  2nd ` ( p ` i )
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
          A. l e. NN0
            A. s e. NN0
              (
                (
                  (
                    l <_ ( # ` A )
                    /\
                    ( VERINA44IntRemainderZero l B )
                  )
                  /\
                  (
                    0 < l
                    /\
                    s <_ ( ( # ` A ) - l )
                  )
                )
                ->
                E. q e. ( 0 ..^ ( # ` p ) )
                  ( p ` q ) = <. l , s >.
              )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina44-impl-sums-definition $a |- (
    VERINA44ImplSums A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA44ImplSumsGraph A B y )
  ) $.
$}

verina44-none-definition $a |- VERINA44None = (/) $.

verina44-some-definition $a |- (
  VERINA44Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina44-option-int-definition $a |- VERINA44OptionInt =
    { x |
      (
        x = VERINA44None
        \/
        E. y e. ZZ x = ( VERINA44Some y )
      )
    } $.
$}

${
  $d i s A B $.

  verina44-best-option-graph-definition $a |- (
    VERINA44BestOptionGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. VERINA44OptionInt
    )
    /\
    (
      (
        A = (/)
        /\
        B = VERINA44None
      )
      \/
      (
        A =/= (/)
        /\
        E. s e. Word ZZ
          (
            (
              (
                ( # ` s ) = ( # ` A )
                /\
                ( s ` 0 ) = ( A ` 0 )
              )
              /\
              A. i e. ( 1 ..^ ( # ` A ) )
                (
                  s ` i
                ) = if (
                  ( s ` ( i - 1 ) ) < ( A ` i ) ,
                  ( A ` i ) ,
                  ( s ` ( i - 1 ) )
                )
            )
            /\
            B = (
              VERINA44Some
                ( s ` ( ( # ` A ) - 1 ) )
            )
          )
      )
    )
  ) $.
$}

${
  $d y A $.

  verina44-best-option-definition $a |- (
    VERINA44BestOption A
  ) = (
    iota_ y e. VERINA44OptionInt
      ( VERINA44BestOptionGraph A y )
  ) $.
$}

verina44-option-get-d-definition $a |- (
  VERINA44OptionGetD A
) = if (
  A = VERINA44None ,
  0 ,
  ( 2nd ` A )
) $.

verina44-precondition-definition $a |- (
  VERINA44Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  0 < B
) $.

verina44-max-subarray-sum-divisible-by-k-definition $a |- (
  VERINA44MaxSubarraySumDivisibleByK A B
) = if (
  (
    ( # ` A ) = 0
    \/
    B = 0
  )
  ,
  0
  ,
  (
    VERINA44OptionGetD
      ( VERINA44BestOption ( VERINA44ImplSums A B ) )
  )
) $.

verina44-to-nat-definition $a |- (
  VERINA44ToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

${
  $d q A B $.

  verina44-post-length-eligible-definition $a |- (
    VERINA44PostLengthEligible A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. ZZ
    )
    /\
    (
      0 < A
      /\
      E. q e. NN0
        A = ( ( VERINA44ToNat B ) x. q )
    )
  ) $.
$}

${
  $d i A B C D $.

  verina44-extract-graph-definition $a |- (
    VERINA44ExtractGraph A B C D
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. Word ZZ
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

  verina44-extract-definition $a |- (
    VERINA44Extract A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINA44ExtractGraph A B C y )
  ) $.
$}

${
  $d i j p q r A B $.

  verina44-post-subarrays-graph-definition $a |- (
    VERINA44PostSubarraysGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
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
                ( 1st ` ( p ` i ) ) < ( # ` A )
                /\
                ( 2nd ` ( p ` i ) ) <_ (
                  ( # ` A ) - ( 1st ` ( p ` i ) )
                )
              )
              /\
              (
                B ` i
              ) = (
                VERINA44Extract
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
          A. q e. NN0
            A. r e. NN0
              (
                (
                  q < ( # ` A )
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

  verina44-post-subarrays-definition $a |- (
    VERINA44PostSubarrays A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA44PostSubarraysGraph A y )
  ) $.
$}

${
  $d i j p A B C $.

  verina44-divisible-subarrays-graph-definition $a |- (
    VERINA44DivisibleSubarraysGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. Word ( Word ZZ )
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
                  # ` ( VERINA44PostSubarrays A )
                )
                /\
                (
                  VERINA44PostLengthEligible
                    (
                      # ` (
                        ( VERINA44PostSubarrays A ) ` ( p ` i )
                      )
                    )
                    B
                )
              )
              /\
              (
                C ` i
              ) = (
                ( VERINA44PostSubarrays A ) ` ( p ` i )
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
            0 ..^ ( # ` ( VERINA44PostSubarrays A ) )
          )
            (
              (
                VERINA44PostLengthEligible
                  (
                    # ` ( ( VERINA44PostSubarrays A ) ` j )
                  )
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

  verina44-divisible-subarrays-definition $a |- (
    VERINA44DivisibleSubarrays A B
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA44DivisibleSubarraysGraph A B y )
  ) $.
$}

verina44-sum-definition $a |- (
  VERINA44Sum A
) = (
  ( VERINA44Prefix A ) ` ( # ` A )
) $.

${
  $d i A B C $.

  verina44-subarray-sums-graph-definition $a |- (
    VERINA44SubarraySumsGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = (
        # ` ( VERINA44DivisibleSubarrays A B )
      )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        (
          C ` i
        ) = (
          VERINA44Sum
            ( ( VERINA44DivisibleSubarrays A B ) ` i )
        )
    )
  ) $.
$}

${
  $d y A B $.

  verina44-subarray-sums-definition $a |- (
    VERINA44SubarraySums A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA44SubarraySumsGraph A B y )
  ) $.
$}

${
  $d i A B C $.

  verina44-postcondition-definition $a |- (
    VERINA44Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. ZZ
    )
    /\
    (
      (
        ( # ` ( VERINA44SubarraySums A B ) ) = 0
        ->
        C = 0
      )
      /\
      (
        0 < ( # ` ( VERINA44SubarraySums A B ) )
        ->
        (
          C e. ran ( VERINA44SubarraySums A B )
          /\
          A. i e. (
            0 ..^ ( # ` ( VERINA44SubarraySums A B ) )
          )
            (
              ( VERINA44SubarraySums A B ) ` i
            ) <_ C
        )
      )
    )
  ) $.
$}

verina-advanced-44-max-subarray-sum-divisible-by-k
  $a |- A. w e. Word ZZ
    A. k e. ZZ
      (
        VERINA44Post
          w
          k
          ( VERINA44MaxSubarraySumDivisibleByK w k )
      )
  $.
