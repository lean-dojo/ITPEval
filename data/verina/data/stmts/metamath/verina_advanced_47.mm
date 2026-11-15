$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_47 (verina__metamath__verina_advanced_47), catalog title
  mergeIntervals: exact recursive insertion sorting and accumulator-based
  interval merging compute a nonoverlapping integer-interval list satisfying
  the source coverage, endpoint, and no-spurious-merge contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA47Interval is exactly Int x Int, and Word VERINA47Interval is the
  type of arbitrary finite lists of integer endpoint pairs. For a word w,
  # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA47IntMax is integer max. VERINA47InsertGraph is the exact local
  insert recursion: its position is the first sorted-list entry whose start
  is at least the inserted interval's start, or the list length if no such
  entry exists. VERINA47SortGraph starts from the empty word and inserts
  source entries from right to left, exactly reproducing the source
  structurally recursive insertion sort. The corresponding iota definitions
  select the unique computed words.

  VERINA47MergeStepGraph is one exact source merge transition on the reversed
  accumulator. An empty accumulator becomes the singleton current interval.
  Otherwise an overlapping current interval replaces the accumulator head
  by the same start and the maximum end, while a disjoint interval is
  prepended. VERINA47MergeAccGraph threads this step through the sorted word,
  VERINA47ReverseGraph is List.reverse, and VERINA47MergeIntervals composes
  the exact sort, merge, and final reverse. It is therefore fixed by the
  executable program rather than chosen from the postcondition.

  VERINA47Pre is exactly List.all (fun (s,e) => s <= e). VERINA47Covered,
  VERINA47NoOverlap, and VERINA47ResultBounded are the first three source
  Boolean checks, expressed by their exact finite quantifier meanings.
  VERINA47NoSpuriousMerge eliminates the local stable filter under List.all:
  for each result interval, every input retained by the filter satisfies
  exactly the source disjunction. This is bidirectionally equivalent because
  List.all depends only on the truth of the predicate for every retained
  occurrence. VERINA47Post is their conjunction. The proof-valued
  precondition argument is computationally and propositionally unused in the
  source implementation and postcondition body, so it is omitted from the
  target functions and predicates. The final $a declaration is the source
  correctness proposition. Every earlier $a is syntax or a faithful
  definition, and this root statement file has no $p declaration.
$)

$c
  VERINA47Interval VERINA47IntMax
  VERINA47InsertGraph VERINA47Insert
  VERINA47SortGraph VERINA47Sort
  VERINA47MergeStepGraph
  VERINA47MergeAccGraph VERINA47MergeAcc
  VERINA47ReverseGraph VERINA47Reverse
  VERINA47Pre VERINA47MergeIntervals
  VERINA47Covered VERINA47NoOverlap
  VERINA47ResultBounded VERINA47NoSpuriousMerge
  VERINA47Post
$.

verina47-interval-syntax
  $a class VERINA47Interval $.
verina47-int-max-syntax
  $a class ( VERINA47IntMax A B ) $.
verina47-insert-graph-syntax
  $a wff ( VERINA47InsertGraph A B C ) $.
verina47-insert-syntax
  $a class ( VERINA47Insert A B ) $.
verina47-sort-graph-syntax
  $a wff ( VERINA47SortGraph A B ) $.
verina47-sort-syntax
  $a class ( VERINA47Sort A ) $.
verina47-merge-step-graph-syntax
  $a wff ( VERINA47MergeStepGraph A B C ) $.
verina47-merge-acc-graph-syntax
  $a wff ( VERINA47MergeAccGraph A B ) $.
verina47-merge-acc-syntax
  $a class ( VERINA47MergeAcc A ) $.
verina47-reverse-graph-syntax
  $a wff ( VERINA47ReverseGraph A B ) $.
verina47-reverse-syntax
  $a class ( VERINA47Reverse A ) $.
verina47-precondition-syntax
  $a wff ( VERINA47Pre A ) $.
verina47-merge-intervals-syntax
  $a class ( VERINA47MergeIntervals A ) $.
verina47-covered-syntax
  $a wff ( VERINA47Covered A B ) $.
verina47-no-overlap-syntax
  $a wff ( VERINA47NoOverlap A ) $.
verina47-result-bounded-syntax
  $a wff ( VERINA47ResultBounded A B ) $.
verina47-no-spurious-merge-syntax
  $a wff ( VERINA47NoSpuriousMerge A B ) $.
verina47-postcondition-syntax
  $a wff ( VERINA47Post A B ) $.

verina47-interval-definition $a |- VERINA47Interval = (
  ZZ X. ZZ
) $.

verina47-int-max-definition $a |- (
  VERINA47IntMax A B
) = if (
  A < B ,
  B ,
  A
) $.

${
  $d j p A B C $.

  verina47-insert-graph-definition $a |- (
    VERINA47InsertGraph A B C
  ) <-> (
    (
      (
        A e. VERINA47Interval
        /\
        B e. Word VERINA47Interval
      )
      /\
      C e. Word VERINA47Interval
    )
    /\
    E. p e. NN0
      (
        p <_ ( # ` B )
        /\
        (
          (
            A. j e. ( 0 ..^ p )
              -. (
                1st ` A
              ) <_ (
                1st ` ( B ` j )
              )
            /\
            (
              p < ( # ` B )
              ->
              (
                1st ` A
              ) <_ (
                1st ` ( B ` p )
              )
            )
          )
          /\
          (
            ( # ` C ) = ( ( # ` B ) + 1 )
            /\
            (
              ( C ` p ) = A
              /\
              (
                A. j e. ( 0 ..^ p )
                  ( C ` j ) = ( B ` j )
                /\
                A. j e. ( p ..^ ( # ` B ) )
                  ( C ` ( j + 1 ) ) = ( B ` j )
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina47-insert-definition $a |- (
    VERINA47Insert A B
  ) = (
    iota_ y e. Word VERINA47Interval
      ( VERINA47InsertGraph A B y )
  ) $.
$}

${
  $d k t A B $.

  verina47-sort-graph-definition $a |- (
    VERINA47SortGraph A B
  ) <-> (
    (
      A e. Word VERINA47Interval
      /\
      B e. Word VERINA47Interval
    )
    /\
    E. t e. Word ( Word VERINA47Interval )
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
              VERINA47InsertGraph
                ( A ` ( ( ( # ` A ) - 1 ) - k ) )
                ( t ` k )
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

  verina47-sort-definition $a |- (
    VERINA47Sort A
  ) = (
    iota_ y e. Word VERINA47Interval
      ( VERINA47SortGraph A y )
  ) $.
$}

${
  $d j A B C $.

  verina47-merge-step-graph-definition $a |- (
    VERINA47MergeStepGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA47Interval
        /\
        B e. VERINA47Interval
      )
      /\
      C e. Word VERINA47Interval
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
                  (
                    VERINA47IntMax
                      ( 2nd ` ( A ` 0 ) )
                      ( 2nd ` B )
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

  verina47-merge-acc-graph-definition $a |- (
    VERINA47MergeAccGraph A B
  ) <-> (
    (
      A e. Word VERINA47Interval
      /\
      B e. Word VERINA47Interval
    )
    /\
    E. t e. Word ( Word VERINA47Interval )
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
              VERINA47MergeStepGraph
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

  verina47-merge-acc-definition $a |- (
    VERINA47MergeAcc A
  ) = (
    iota_ y e. Word VERINA47Interval
      ( VERINA47MergeAccGraph A y )
  ) $.
$}

${
  $d i A B $.

  verina47-reverse-graph-definition $a |- (
    VERINA47ReverseGraph A B
  ) <-> (
    (
      A e. Word VERINA47Interval
      /\
      B e. Word VERINA47Interval
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

  verina47-reverse-definition $a |- (
    VERINA47Reverse A
  ) = (
    iota_ y e. Word VERINA47Interval
      ( VERINA47ReverseGraph A y )
  ) $.
$}

${
  $d i A $.

  verina47-precondition-definition $a |- (
    VERINA47Pre A
  ) <-> (
    (
      A e. Word VERINA47Interval
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          1st ` ( A ` i )
        ) <_ (
          2nd ` ( A ` i )
        )
    )
  ) $.
$}

verina47-merge-intervals-definition $a |- (
  VERINA47MergeIntervals A
) = (
  VERINA47Reverse
    (
      VERINA47MergeAcc
        ( VERINA47Sort A )
    )
) $.

${
  $d i j A B $.

  verina47-covered-definition $a |- (
    VERINA47Covered A B
  ) <-> (
    (
      A e. Word VERINA47Interval
      /\
      B e. Word VERINA47Interval
    )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      E. j e. ( 0 ..^ ( # ` B ) )
        (
          (
            1st ` ( B ` j )
          ) <_ (
            1st ` ( A ` i )
          )
          /\
          (
            2nd ` ( A ` i )
          ) <_ (
            2nd ` ( B ` j )
          )
        )
  ) $.
$}

${
  $d i A $.

  verina47-no-overlap-definition $a |- (
    VERINA47NoOverlap A
  ) <-> (
    (
      A e. Word VERINA47Interval
      /\
      A. i e. ( 0 ..^ ( ( # ` A ) - 1 ) )
        (
          2nd ` ( A ` i )
        ) < (
          1st ` ( A ` ( i + 1 ) )
        )
    )
  ) $.
$}

${
  $d i j k A B $.

  verina47-result-bounded-definition $a |- (
    VERINA47ResultBounded A B
  ) <-> (
    (
      A e. Word VERINA47Interval
      /\
      B e. Word VERINA47Interval
    )
    /\
    A. i e. ( 0 ..^ ( # ` B ) )
      (
        E. j e. ( 0 ..^ ( # ` A ) )
          (
            1st ` ( A ` j )
          ) = (
            1st ` ( B ` i )
          )
        /\
        E. k e. ( 0 ..^ ( # ` A ) )
          (
            2nd ` ( A ` k )
          ) = (
            2nd ` ( B ` i )
          )
      )
  ) $.
$}

${
  $d i j k A B $.

  verina47-no-spurious-merge-definition $a |- (
    VERINA47NoSpuriousMerge A B
  ) <-> (
    (
      A e. Word VERINA47Interval
      /\
      B e. Word VERINA47Interval
    )
    /\
    A. i e. ( 0 ..^ ( # ` B ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          (
            (
              1st ` ( B ` i )
            ) <_ (
              1st ` ( A ` j )
            )
            /\
            (
              2nd ` ( A ` j )
            ) <_ (
              2nd ` ( B ` i )
            )
          )
          ->
          (
            (
              1st ` ( A ` j )
            ) = (
              1st ` ( B ` i )
            )
            \/
            E. k e. ( 0 ..^ ( # ` A ) )
              (
                (
                  (
                    1st ` ( B ` i )
                  ) <_ (
                    1st ` ( A ` k )
                  )
                  /\
                  (
                    2nd ` ( A ` k )
                  ) <_ (
                    2nd ` ( B ` i )
                  )
                )
                /\
                (
                  (
                    1st ` ( A ` k )
                  ) < (
                    1st ` ( A ` j )
                  )
                  /\
                  (
                    1st ` ( A ` j )
                  ) <_ (
                    2nd ` ( A ` k )
                  )
                )
              )
          )
        )
  ) $.
$}

verina47-postcondition-definition $a |- (
  VERINA47Post A B
) <-> (
  (
    A e. Word VERINA47Interval
    /\
    B e. Word VERINA47Interval
  )
  /\
  (
    (
      ( VERINA47Covered A B )
      /\
      ( VERINA47NoOverlap B )
    )
    /\
    (
      ( VERINA47ResultBounded A B )
      /\
      ( VERINA47NoSpuriousMerge A B )
    )
  )
) $.

verina-advanced-47-merge-intervals
  $a |- A. w e. Word VERINA47Interval
    (
      ( VERINA47Pre w )
      ->
      (
        VERINA47Post
          w
          ( VERINA47MergeIntervals w )
      )
    )
  $.
