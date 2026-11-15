$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_28 (verina__metamath__verina_advanced_28), catalog title
  longestConsecutive: the exact hash-set and bounded-loop program returns the
  maximum length of a consecutive-integer streak, with its independently
  sorted-sublist correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  After the source insertion loop, HashSet membership is extensionally
  exactly membership in ran nums; capacity and bucket layout are unobservable.
  VERINA28RunLengthGraph reproduces the bounded inner loop. Its witness m is
  the number of successful successor tests, capped at nums.length: offsets
  one through m are present, and either all iterations were used or the next
  successor is absent. The returned length is m + 1.
  VERINA28LongestGraph threads maxLen through nums in source order, skipping
  entries whose predecessor is present and otherwise taking Nat.max with the
  exact inner-loop result. VERINA28LongestConsecutive selects the unique final
  value, so the implementation is not chosen from the postcondition.

  VERINA28Nodup is List.Nodup and VERINA28Pre is the source precondition.
  VERINA28MergeSortGraph characterizes the unique nondecreasing permutation
  of an integer word, which is extensionally exactly List.mergeSort on the
  source total order. VERINA28Extract is the exact valid-range List.extract
  used by the postcondition. VERINA28IsConsecutive reproduces the source
  Boolean test: the empty word succeeds, and otherwise every indexed entry is
  the first entry plus its index.

  VERINA28ConsecutiveLensGraph enumerates pairs (start,len) in the same
  lexicographic order as the source flatMap of its two List.range values,
  retains exactly those whose sorted extraction is consecutive, and maps each
  retained extraction to len. It therefore preserves every occurrence and
  the exact order of consec_sublist_lens. VERINA28Post reproduces the empty
  branch, List.contains, and List.all. The proof-valued precondition argument
  is computationally and propositionally unused and is omitted from the
  target function and postcondition predicate. The final $a declaration is
  the source correctness proposition. Every earlier $a is syntax or a
  faithful definition, and this database has no $p declaration.
$)

$c
  VERINA28Nodup VERINA28Pre
  VERINA28RunLengthGraph VERINA28RunLength
  VERINA28LongestGraph VERINA28LongestConsecutive
  VERINA28MergeSortGraph VERINA28MergeSort
  VERINA28ExtractGraph VERINA28Extract
  VERINA28IsConsecutive
  VERINA28ConsecutiveLensGraph VERINA28ConsecutiveLens
  VERINA28Post
$.

verina28-nodup-syntax
  $a wff ( VERINA28Nodup A ) $.
verina28-precondition-syntax
  $a wff ( VERINA28Pre A ) $.
verina28-run-length-graph-syntax
  $a wff ( VERINA28RunLengthGraph A B C ) $.
verina28-run-length-syntax
  $a class ( VERINA28RunLength A B ) $.
verina28-longest-graph-syntax
  $a wff ( VERINA28LongestGraph A B ) $.
verina28-longest-consecutive-syntax
  $a class ( VERINA28LongestConsecutive A ) $.
verina28-merge-sort-graph-syntax
  $a wff ( VERINA28MergeSortGraph A B ) $.
verina28-merge-sort-syntax
  $a class ( VERINA28MergeSort A ) $.
verina28-extract-graph-syntax
  $a wff ( VERINA28ExtractGraph A B C D ) $.
verina28-extract-syntax
  $a class ( VERINA28Extract A B C ) $.
verina28-is-consecutive-syntax
  $a wff ( VERINA28IsConsecutive A ) $.
verina28-consecutive-lens-graph-syntax
  $a wff ( VERINA28ConsecutiveLensGraph A B ) $.
verina28-consecutive-lens-syntax
  $a class ( VERINA28ConsecutiveLens A ) $.
verina28-postcondition-syntax
  $a wff ( VERINA28Post A B ) $.

${
  $d i j A $.

  verina28-nodup-definition $a |- (
    VERINA28Nodup A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i =/= j
            ->
            ( A ` i ) =/= ( A ` j )
          )
    )
  ) $.
$}

verina28-precondition-definition $a |- (
  VERINA28Pre A
) <-> (
  (
    A e. Word ZZ
    /\
    ( VERINA28Nodup A )
  )
) $.

${
  $d k m A B C $.

  verina28-run-length-graph-definition $a |- (
    VERINA28RunLengthGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. NN0
    )
    /\
    E. m e. NN0
      (
        (
          m <_ ( # ` A )
          /\
          C = ( m + 1 )
        )
        /\
        (
          A. k e. ( 1 ..^ ( m + 1 ) )
            ( B + k ) e. ran A
          /\
          (
            m = ( # ` A )
            \/
            -. ( ( B + ( m + 1 ) ) e. ran A )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina28-run-length-definition $a |- (
    VERINA28RunLength A B
  ) = (
    iota_ y e. NN0
      ( VERINA28RunLengthGraph A B y )
  ) $.
$}

${
  $d k t A B $.

  verina28-longest-graph-definition $a |- (
    VERINA28LongestGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    E. t e. Word NN0
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              t ` ( k + 1 )
            ) = if (
              -. ( ( ( A ` k ) - 1 ) e. ran A ) ,
              if (
                ( t ` k ) < (
                  VERINA28RunLength A ( A ` k )
                ) ,
                ( VERINA28RunLength A ( A ` k ) ) ,
                ( t ` k )
              ) ,
              ( t ` k )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina28-longest-consecutive-definition $a |- (
    VERINA28LongestConsecutive A
  ) = (
    iota_ y e. NN0
      ( VERINA28LongestGraph A y )
  ) $.
$}

${
  $d i j x A B $.

  verina28-merge-sort-graph-definition $a |- (
    VERINA28MergeSortGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      (
        A. i e. ( 0 ..^ ( # ` B ) )
          A. j e. ( 0 ..^ ( # ` B ) )
            (
              i < j
              ->
              ( B ` i ) <_ ( B ` j )
            )
      )
      /\
      A. x e. ZZ
        (
          # ` {
            i e. ( 0 ..^ ( # ` A ) )
            |
            ( A ` i ) = x
          }
        ) = (
          # ` {
            j e. ( 0 ..^ ( # ` B ) )
            |
            ( B ` j ) = x
          }
        )
    )
  ) $.
$}

${
  $d y A $.

  verina28-merge-sort-definition $a |- (
    VERINA28MergeSort A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA28MergeSortGraph A y )
  ) $.
$}

${
  $d i A B C D $.

  verina28-extract-graph-definition $a |- (
    VERINA28ExtractGraph A B C D
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

  verina28-extract-definition $a |- (
    VERINA28Extract A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINA28ExtractGraph A B C y )
  ) $.
$}

${
  $d i A $.

  verina28-is-consecutive-definition $a |- (
    VERINA28IsConsecutive A
  ) <-> (
    (
      A e. Word ZZ
      /\
      (
        A = (/)
        \/
        A. i e. ( 0 ..^ ( # ` A ) )
          ( A ` i ) = ( ( A ` 0 ) + i )
      )
    )
  ) $.
$}

${
  $d i j k p q A B $.

  verina28-consecutive-lens-graph-definition $a |- (
    VERINA28ConsecutiveLensGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word NN0
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
                VERINA28IsConsecutive
                  (
                    VERINA28Extract
                      ( VERINA28MergeSort A )
                      ( 1st ` ( p ` i ) )
                      ( 2nd ` ( p ` i ) )
                  )
                /\
                ( B ` i ) = ( 2nd ` ( p ` i ) )
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
          A. q e. ( 0 ..^ ( # ` A ) )
            A. k e. (
              0 ..^ ( ( ( # ` A ) - q ) + 1 )
            )
              (
                VERINA28IsConsecutive
                  (
                    VERINA28Extract
                      ( VERINA28MergeSort A )
                      q
                      k
                  )
                ->
                E. i e. ( 0 ..^ ( # ` p ) )
                  ( p ` i ) = <. q , k >.
              )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina28-consecutive-lens-definition $a |- (
    VERINA28ConsecutiveLens A
  ) = (
    iota_ y e. Word NN0
      ( VERINA28ConsecutiveLensGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina28-postcondition-definition $a |- (
    VERINA28Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    (
      (
        A = (/)
        ->
        B = 0
      )
      /\
      (
        A =/= (/)
        ->
        (
          B e. ran ( VERINA28ConsecutiveLens A )
          /\
          A. k e. (
            0 ..^ ( # ` ( VERINA28ConsecutiveLens A ) )
          )
            (
              ( VERINA28ConsecutiveLens A ) ` k
            ) <_ B
        )
      )
    )
  ) $.
$}

verina-advanced-28-longest-consecutive
  $a |- A. w e. Word ZZ
    (
      ( VERINA28Pre w )
      ->
      (
        VERINA28Post
          w
          ( VERINA28LongestConsecutive w )
      )
    )
  $.
