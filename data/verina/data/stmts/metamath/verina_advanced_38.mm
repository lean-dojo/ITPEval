$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_38 (verina__metamath__verina_advanced_38), catalog title
  maxCoverageAfterRemovingOne: the exact erase, stable merge-sort, interval-
  merge, coverage-sum, and maximum-fold program computes the greatest
  coverage obtained by removing one interval from an arbitrary nonempty
  finite list of natural-number intervals. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA38Interval is exactly Nat x Nat, and Word VERINA38Interval is the
  type of arbitrary finite lists of natural-number endpoint pairs. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA38EraseIdxGraph reproduces List.eraseIdx, including its unchanged
  result for an out-of-range index. VERINA38MergeSortGraph uses a permutation
  of source indices ordered by left endpoint and then by original position.
  This is exactly the stable List.mergeSort with comparator
  fun a b => a.1 <= b.1, including the ordering of equal-left-endpoint
  intervals.

  VERINA38MergeStepGraph is the source fold step on its reversed accumulator:
  an empty accumulator becomes the singleton current interval; otherwise the
  current interval either extends the accumulator head using Nat.max, or is
  prepended as a new component. VERINA38MergedGraph threads that step through
  the sorted word exactly as List.foldl. VERINA38ReverseGraph is List.reverse,
  and VERINA38CoverageGraph is the final foldl summing Lean's Nat.sub spans
  from zero. SetMM's ordinary subtraction is guarded explicitly: an endpoint
  pair with end < start contributes zero, and otherwise contributes
  end - start.

  VERINA38CoverageAfterRemoving composes those exact helpers for one index.
  VERINA38MaxFoldGraph threads Nat.max through List.range intervals.length,
  and VERINA38MaxCoverageAfterRemovingOne preserves the source length-at-most-
  one branch. Thus the implementation is fixed independently of the
  postcondition.

  VERINA38Pre is the positive-length precondition. VERINA38Post requires an
  in-range removal index attaining the result and compares its exact coverage
  against every other in-range removal, matching the source existential and
  universal scopes. The proof-valued precondition argument is computationally
  and propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this root statement
  file introduces no $p declaration.
$)

$c
  VERINA38Interval
  VERINA38EraseIdxGraph VERINA38EraseIdx
  VERINA38MergeSortGraph VERINA38MergeSort
  VERINA38MergeStepGraph
  VERINA38MergedGraph VERINA38Merged
  VERINA38ReverseGraph VERINA38Reverse
  VERINA38CoverageGraph VERINA38Coverage
  VERINA38CoverageAfterRemoving
  VERINA38MaxFoldGraph VERINA38MaxFold
  VERINA38Pre VERINA38MaxCoverageAfterRemovingOne VERINA38Post
$.

verina38-interval-syntax
  $a class VERINA38Interval $.
verina38-erase-idx-graph-syntax
  $a wff ( VERINA38EraseIdxGraph A B C ) $.
verina38-erase-idx-syntax
  $a class ( VERINA38EraseIdx A B ) $.
verina38-merge-sort-graph-syntax
  $a wff ( VERINA38MergeSortGraph A B ) $.
verina38-merge-sort-syntax
  $a class ( VERINA38MergeSort A ) $.
verina38-merge-step-graph-syntax
  $a wff ( VERINA38MergeStepGraph A B C ) $.
verina38-merged-graph-syntax
  $a wff ( VERINA38MergedGraph A B ) $.
verina38-merged-syntax
  $a class ( VERINA38Merged A ) $.
verina38-reverse-graph-syntax
  $a wff ( VERINA38ReverseGraph A B ) $.
verina38-reverse-syntax
  $a class ( VERINA38Reverse A ) $.
verina38-coverage-graph-syntax
  $a wff ( VERINA38CoverageGraph A B ) $.
verina38-coverage-syntax
  $a class ( VERINA38Coverage A ) $.
verina38-coverage-after-removing-syntax
  $a class ( VERINA38CoverageAfterRemoving A B ) $.
verina38-max-fold-graph-syntax
  $a wff ( VERINA38MaxFoldGraph A B ) $.
verina38-max-fold-syntax
  $a class ( VERINA38MaxFold A ) $.
verina38-precondition-syntax
  $a wff ( VERINA38Pre A ) $.
verina38-max-coverage-syntax
  $a class ( VERINA38MaxCoverageAfterRemovingOne A ) $.
verina38-postcondition-syntax
  $a wff ( VERINA38Post A B ) $.

verina38-interval-definition $a |- VERINA38Interval = (
  NN0 X. NN0
) $.

${
  $d j A B C $.

  verina38-erase-idx-graph-definition $a |- (
    VERINA38EraseIdxGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA38Interval
        /\
        B e. NN0
      )
      /\
      C e. Word VERINA38Interval
    )
    /\
    (
      (
        B < ( # ` A )
        /\
        (
          ( # ` C ) = ( ( # ` A ) - 1 )
          /\
          (
            A. j e. ( 0 ..^ B )
              ( C ` j ) = ( A ` j )
            /\
            A. j e. ( B ..^ ( # ` C ) )
              ( C ` j ) = ( A ` ( j + 1 ) )
          )
        )
      )
      \/
      (
        ( # ` A ) <_ B
        /\
        C = A
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina38-erase-idx-definition $a |- (
    VERINA38EraseIdx A B
  ) = (
    iota_ y e. Word VERINA38Interval
      ( VERINA38EraseIdxGraph A B y )
  ) $.
$}

${
  $d i j p A B $.

  verina38-merge-sort-graph-definition $a |- (
    VERINA38MergeSortGraph A B
  ) <-> (
    (
      A e. Word VERINA38Interval
      /\
      B e. Word VERINA38Interval
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( # ` A )
          /\
          ( # ` B ) = ( # ` A )
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              ( p ` i ) < ( # ` A )
              /\
              ( B ` i ) = ( A ` ( p ` i ) )
            )
          /\
          (
            A. i e. ( 0 ..^ ( # ` A ) )
              A. j e. ( 0 ..^ ( # ` A ) )
                (
                  i =/= j
                  ->
                  ( p ` i ) =/= ( p ` j )
                )
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              A. j e. ( 0 ..^ ( # ` A ) )
                (
                  i < j
                  ->
                  (
                    (
                      1st ` ( B ` i )
                    ) < (
                      1st ` ( B ` j )
                    )
                    \/
                    (
                      (
                        1st ` ( B ` i )
                      ) = (
                        1st ` ( B ` j )
                      )
                      /\
                      ( p ` i ) < ( p ` j )
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

  verina38-merge-sort-definition $a |- (
    VERINA38MergeSort A
  ) = (
    iota_ y e. Word VERINA38Interval
      ( VERINA38MergeSortGraph A y )
  ) $.
$}

${
  $d j A B C $.

  verina38-merge-step-graph-definition $a |- (
    VERINA38MergeStepGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA38Interval
        /\
        B e. VERINA38Interval
      )
      /\
      C e. Word VERINA38Interval
    )
    /\
    (
      (
        A = (/)
        /\
        (
          ( # ` C ) = 1
          /\
          ( C ` 0 ) = B
        )
      )
      \/
      (
        A =/= (/)
        /\
        (
          (
            (
              1st ` B
            ) <_ (
              2nd ` ( A ` 0 )
            )
            /\
            (
              ( # ` C ) = ( # ` A )
              /\
              (
                ( C ` 0 ) = <.
                  ( 1st ` ( A ` 0 ) ) ,
                  if (
                    (
                      2nd ` ( A ` 0 )
                    ) < (
                      2nd ` B
                    ) ,
                    ( 2nd ` B ) ,
                    ( 2nd ` ( A ` 0 ) )
                  )
                >.
                /\
                A. j e. ( 1 ..^ ( # ` A ) )
                  ( C ` j ) = ( A ` j )
              )
            )
          )
          \/
          (
            (
              2nd ` ( A ` 0 )
            ) < (
              1st ` B
            )
            /\
            (
              ( # ` C ) = ( ( # ` A ) + 1 )
              /\
              (
                ( C ` 0 ) = B
                /\
                A. j e. ( 0 ..^ ( # ` A ) )
                  ( C ` ( j + 1 ) ) = ( A ` j )
              )
            )
          )
        )
      )
    )
  ) $.
$}

${
  $d k t A B $.

  verina38-merged-graph-definition $a |- (
    VERINA38MergedGraph A B
  ) <-> (
    (
      A e. Word VERINA38Interval
      /\
      B e. Word VERINA38Interval
    )
    /\
    E. t e. Word ( Word VERINA38Interval )
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
              VERINA38MergeStepGraph
                ( t ` k )
                ( A ` k )
                ( t ` ( k + 1 ) )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina38-merged-definition $a |- (
    VERINA38Merged A
  ) = (
    iota_ y e. Word VERINA38Interval
      ( VERINA38MergedGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina38-reverse-graph-definition $a |- (
    VERINA38ReverseGraph A B
  ) <-> (
    (
      A e. Word VERINA38Interval
      /\
      B e. Word VERINA38Interval
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

  verina38-reverse-definition $a |- (
    VERINA38Reverse A
  ) = (
    iota_ y e. Word VERINA38Interval
      ( VERINA38ReverseGraph A y )
  ) $.
$}

${
  $d k s A B $.

  verina38-coverage-graph-definition $a |- (
    VERINA38CoverageGraph A B
  ) <-> (
    (
      A e. Word VERINA38Interval
      /\
      B e. NN0
    )
    /\
    E. s e. Word NN0
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( k + 1 )
            ) = (
              ( s ` k )
              + if (
                (
                  2nd ` ( A ` k )
                ) < (
                  1st ` ( A ` k )
                ) ,
                0 ,
                (
                  ( 2nd ` ( A ` k ) )
                  -
                  ( 1st ` ( A ` k ) )
                )
              )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina38-coverage-definition $a |- (
    VERINA38Coverage A
  ) = (
    iota_ y e. NN0
      ( VERINA38CoverageGraph A y )
  ) $.
$}

verina38-coverage-after-removing-definition $a |- (
  VERINA38CoverageAfterRemoving A B
) = (
  VERINA38Coverage
    (
      VERINA38Reverse
        (
          VERINA38Merged
            (
              VERINA38MergeSort
                ( VERINA38EraseIdx A B )
            )
        )
    )
) $.

${
  $d k s A B $.

  verina38-max-fold-graph-definition $a |- (
    VERINA38MaxFoldGraph A B
  ) <-> (
    (
      A e. Word VERINA38Interval
      /\
      B e. NN0
    )
    /\
    E. s e. Word NN0
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( k + 1 )
            ) = if (
              ( s ` k ) < (
                VERINA38CoverageAfterRemoving A k
              ) ,
              ( VERINA38CoverageAfterRemoving A k ) ,
              ( s ` k )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina38-max-fold-definition $a |- (
    VERINA38MaxFold A
  ) = (
    iota_ y e. NN0
      ( VERINA38MaxFoldGraph A y )
  ) $.
$}

verina38-precondition-definition $a |- (
  VERINA38Pre A
) <-> (
  (
    A e. Word VERINA38Interval
    /\
    0 < ( # ` A )
  )
) $.

verina38-max-coverage-definition $a |- (
  VERINA38MaxCoverageAfterRemovingOne A
) = if (
  ( # ` A ) <_ 1 ,
  0 ,
  ( VERINA38MaxFold A )
) $.

${
  $d i j A B $.

  verina38-postcondition-definition $a |- (
    VERINA38Post A B
  ) <-> (
    (
      (
        A e. Word VERINA38Interval
        /\
        B e. NN0
      )
      /\
      0 < ( # ` A )
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      (
        B = (
          VERINA38CoverageAfterRemoving A i
        )
        /\
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            VERINA38CoverageAfterRemoving A j
          ) <_ (
            VERINA38CoverageAfterRemoving A i
          )
      )
  ) $.
$}

verina-advanced-38-max-coverage-after-removing-one
  $a |- A. w e. Word VERINA38Interval
    (
      ( VERINA38Pre w )
      ->
      (
        VERINA38Post
          w
          ( VERINA38MaxCoverageAfterRemovingOne w )
      )
    )
  $.
