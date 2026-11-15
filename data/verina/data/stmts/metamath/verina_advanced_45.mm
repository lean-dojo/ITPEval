$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_45 (verina__metamath__verina_advanced_45), catalog title
  maxSubarraySum: the exact recursive Kadane scan computes an integer result
  for every finite integer list, with the independently enumerated
  nonempty-contiguous-subarray maximum postcondition and the empty-list
  result zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  i ..^ j is the half-open natural interval from i through j - 1.

  VERINA45IntMax is integer max. VERINA45HelperGraph is the exact complete
  trace of the source local recursive helper on arbitrary helper arguments.
  Its c and g words record curMax and globalMax before and after every
  consumed entry. Each transition computes
    newCurMax = max x (curMax + x)
  and then
    newGlobal = max globalMax newCurMax.
  VERINA45Helper selects the final global maximum from that unique trace.

  VERINA45NatSub restores Lean's truncated Nat.sub on natural arguments.
  VERINA45TailGraph and VERINA45Tail give List.tail, including the empty-list
  case. VERINA45MaxSubarraySum is the exact source match: it returns integer
  zero on the empty word, and otherwise invokes the helper on the tail with
  both initial maxima equal to the head.

  VERINA45PrefixGraph records the unique integer prefix sums starting at
  zero. VERINA45SubarraySumsGraph reproduces the source postcondition's
  List.range and List.range' flatMap order. Its index-pair word lists, in
  increasing start and then increasing positive length, every pair with
  start + length at most the input length. Each output is the sum of exactly
  the same drop/take contiguous subarray, expressed as a prefix difference;
  duplicate sums are retained.

  VERINA45Pre is the source True precondition together with the List Int
  input type. VERINA45Post preserves the source match: an empty input
  requires result zero, while a nonempty input requires the result to occur
  in the independently generated subarray-sum word and to bound every entry
  above. The proof-valued precondition argument is computationally and
  propositionally unused and is omitted from the target function and
  postcondition predicate. The final $a declaration is the source
  correctness proposition. Every earlier $a is syntax or a faithful
  definition, and this database has no $p declaration.
$)

$c
  VERINA45IntMax
  VERINA45HelperGraph VERINA45Helper
  VERINA45NatSub
  VERINA45TailGraph VERINA45Tail
  VERINA45Pre VERINA45MaxSubarraySum
  VERINA45PrefixGraph VERINA45Prefix
  VERINA45SubarraySumsGraph VERINA45SubarraySums
  VERINA45Post
$.

verina45-int-max-syntax
  $a class ( VERINA45IntMax A B ) $.
verina45-helper-graph-syntax
  $a wff ( VERINA45HelperGraph A B C D ) $.
verina45-helper-syntax
  $a class ( VERINA45Helper A B C ) $.
verina45-nat-sub-syntax
  $a class ( VERINA45NatSub A B ) $.
verina45-tail-graph-syntax
  $a wff ( VERINA45TailGraph A B ) $.
verina45-tail-syntax
  $a class ( VERINA45Tail A ) $.
verina45-precondition-syntax
  $a wff ( VERINA45Pre A ) $.
verina45-max-subarray-sum-syntax
  $a class ( VERINA45MaxSubarraySum A ) $.
verina45-prefix-graph-syntax
  $a wff ( VERINA45PrefixGraph A B ) $.
verina45-prefix-syntax
  $a class ( VERINA45Prefix A ) $.
verina45-subarray-sums-graph-syntax
  $a wff ( VERINA45SubarraySumsGraph A B ) $.
verina45-subarray-sums-syntax
  $a class ( VERINA45SubarraySums A ) $.
verina45-postcondition-syntax
  $a wff ( VERINA45Post A B ) $.

verina45-int-max-definition $a |- (
  VERINA45IntMax A B
) = if (
  A < B ,
  B ,
  A
) $.

${
  $d k c g A B C D $.

  verina45-helper-graph-definition $a |- (
    VERINA45HelperGraph A B C D
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
    E. c e. Word ZZ
      E. g e. Word ZZ
        (
          (
            (
              ( # ` c ) = ( ( # ` A ) + 1 )
              /\
              ( # ` g ) = ( ( # ` A ) + 1 )
            )
            /\
            (
              ( c ` 0 ) = B
              /\
              ( g ` 0 ) = C
            )
          )
          /\
          (
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                (
                  c ` ( k + 1 )
                ) = (
                  VERINA45IntMax
                    ( A ` k )
                    ( ( c ` k ) + ( A ` k ) )
                )
                /\
                (
                  g ` ( k + 1 )
                ) = (
                  VERINA45IntMax
                    ( g ` k )
                    ( c ` ( k + 1 ) )
                )
              )
            /\
            D = ( g ` ( # ` A ) )
          )
        )
  ) $.
$}

${
  $d y A B C $.

  verina45-helper-definition $a |- (
    VERINA45Helper A B C
  ) = (
    iota_ y e. ZZ
      ( VERINA45HelperGraph A B C y )
  ) $.
$}

verina45-nat-sub-definition $a |- (
  VERINA45NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d j A B $.

  verina45-tail-graph-definition $a |- (
    VERINA45TailGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( VERINA45NatSub ( # ` A ) 1 )
      /\
      A. j e. ( 0 ..^ ( # ` B ) )
        ( B ` j ) = ( A ` ( j + 1 ) )
    )
  ) $.
$}

${
  $d y A $.

  verina45-tail-definition $a |- (
    VERINA45Tail A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA45TailGraph A y )
  ) $.
$}

verina45-precondition-definition $a |- (
  VERINA45Pre A
) <-> (
  A e. Word ZZ
) $.

verina45-max-subarray-sum-definition $a |- (
  VERINA45MaxSubarraySum A
) = if (
  ( # ` A ) = 0 ,
  0 ,
  (
    VERINA45Helper
      ( VERINA45Tail A )
      ( A ` 0 )
      ( A ` 0 )
  )
) $.

${
  $d i A B $.

  verina45-prefix-graph-definition $a |- (
    VERINA45PrefixGraph A B
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

  verina45-prefix-definition $a |- (
    VERINA45Prefix A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA45PrefixGraph A y )
  ) $.
$}

${
  $d i j l p q s A B $.

  verina45-subarray-sums-graph-definition $a |- (
    VERINA45SubarraySumsGraph A B
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
                (
                  ( 1st ` ( p ` i ) ) < ( # ` A )
                  /\
                  0 < ( 2nd ` ( p ` i ) )
                )
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
                  VERINA45Prefix A
                ) ` (
                  ( 1st ` ( p ` i ) ) +
                  ( 2nd ` ( p ` i ) )
                )
                -
                (
                  VERINA45Prefix A
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
                  (
                    s < ( # ` A )
                    /\
                    0 < l
                  )
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

  verina45-subarray-sums-definition $a |- (
    VERINA45SubarraySums A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA45SubarraySumsGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina45-postcondition-definition $a |- (
    VERINA45Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      (
        ( # ` A ) = 0
        /\
        B = 0
      )
      \/
      (
        0 < ( # ` A )
        /\
        (
          B e. ran ( VERINA45SubarraySums A )
          /\
          A. i e. (
            0 ..^ ( # ` ( VERINA45SubarraySums A ) )
          )
            (
              ( VERINA45SubarraySums A ) ` i
            ) <_ B
        )
      )
    )
  ) $.
$}

verina-advanced-45-max-subarray-sum
  $a |- A. w e. Word ZZ
    (
      ( VERINA45Pre w )
      ->
      (
        VERINA45Post
          w
          ( VERINA45MaxSubarraySum w )
      )
    )
  $.
