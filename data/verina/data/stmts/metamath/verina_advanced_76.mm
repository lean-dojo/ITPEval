$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_76 (verina__metamath__verina_advanced_76), catalog title
  topKFrequent: the exact first-occurrence frequency fold, stable descending
  insertion sort, and take-and-project computation return the requested
  number of most frequent integers with the complete correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains.
  Word ZZ is exactly the type of arbitrary finite integer lists, and
  VERINA76Pair is the source pair type Int x Nat. For a word w, # ` w is
  its natural-number length, w ` i is zero-based lookup, ran w is its entry
  set, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA76Count is Lean's List.count with integer equality.
  VERINA76FrequencyUpdateGraph is one exact step of the source freqList
  fold. If find? sees a matching key, the source map increments every
  matching pair and preserves every other pair. If no key matches, the
  source append adds the pair (n, 1). VERINA76FrequencyListGraph records the
  complete left-to-right fold trace from the empty word, and
  VERINA76FrequencyList selects its unique result. In particular, its pairs
  have distinct keys in first-occurrence order, exactly as in the program.

  VERINA76InsertSortedGraph is the exact local insertSorted recursion. The
  insertion position is the first accumulated pair with a strictly smaller
  count, or the word length when none exists. Thus equal-count pairs remain
  in their previous order. VERINA76SortedGraph records the source foldl over
  freqList from the empty word, and VERINA76Sorted selects its unique stable
  descending-frequency result.

  VERINA76TakeKeysGraph reproduces sorted.take k followed by mapping first
  projections, including arbitrary natural k. VERINA76TopKFrequentGraph
  explicitly composes the frequency fold, sorting fold, and take-and-project
  graph, so VERINA76TopKFrequent is fixed by the executable computation
  independently of the postcondition and permits no extra outputs.

  VERINA76DistinctCount is nums.eraseDups.length, equivalently the finite
  cardinality of ran nums. VERINA76Pre is exactly k <= that length.
  VERINA76Post preserves result length k, membership in nums, pairwise
  distinctness, the nested result.all/nums.all frequency-dominance clause,
  and List.Pairwise on result.zipIdx, expanded over all earlier and later
  result positions. The proof-valued precondition arguments are
  computationally and propositionally unused and are represented by the
  explicit antecedent of the final correctness assertion. Every earlier $a
  is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINA76Pair VERINA76NatMin VERINA76Count
  VERINA76FrequencyUpdateGraph
  VERINA76FrequencyListGraph VERINA76FrequencyList
  VERINA76InsertSortedGraph
  VERINA76SortedGraph VERINA76Sorted
  VERINA76TakeKeysGraph VERINA76TakeKeys
  VERINA76TopKFrequentGraph VERINA76TopKFrequent
  VERINA76DistinctCount VERINA76Pre VERINA76Post
$.

verina76-pair-syntax
  $a class VERINA76Pair $.
verina76-nat-min-syntax
  $a class ( VERINA76NatMin A B ) $.
verina76-count-syntax
  $a class ( VERINA76Count A B ) $.
verina76-frequency-update-graph-syntax
  $a wff ( VERINA76FrequencyUpdateGraph A B C ) $.
verina76-frequency-list-graph-syntax
  $a wff ( VERINA76FrequencyListGraph A B ) $.
verina76-frequency-list-syntax
  $a class ( VERINA76FrequencyList A ) $.
verina76-insert-sorted-graph-syntax
  $a wff ( VERINA76InsertSortedGraph A B C ) $.
verina76-sorted-graph-syntax
  $a wff ( VERINA76SortedGraph A B ) $.
verina76-sorted-syntax
  $a class ( VERINA76Sorted A ) $.
verina76-take-keys-graph-syntax
  $a wff ( VERINA76TakeKeysGraph A B C ) $.
verina76-take-keys-syntax
  $a class ( VERINA76TakeKeys A B ) $.
verina76-top-k-frequent-graph-syntax
  $a wff ( VERINA76TopKFrequentGraph A B C ) $.
verina76-top-k-frequent-syntax
  $a class ( VERINA76TopKFrequent A B ) $.
verina76-distinct-count-syntax
  $a class ( VERINA76DistinctCount A ) $.
verina76-precondition-syntax
  $a wff ( VERINA76Pre A B ) $.
verina76-postcondition-syntax
  $a wff ( VERINA76Post A B C ) $.

verina76-pair-definition $a |- VERINA76Pair = (
  ZZ X. NN0
) $.

verina76-nat-min-definition $a |- (
  VERINA76NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

${
  $d i A B $.

  verina76-count-definition $a |- (
    VERINA76Count A B
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( A ` i ) = B
    }
  ) $.
$}

${
  $d i j A B C $.

  verina76-frequency-update-graph-definition $a |- (
    VERINA76FrequencyUpdateGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA76Pair
        /\
        B e. ZZ
      )
      /\
      C e. Word VERINA76Pair
    )
    /\
    (
      (
        E. j e. ( 0 ..^ ( # ` A ) )
          ( 1st ` ( A ` j ) ) = B
        /\
        (
          ( # ` C ) = ( # ` A )
          /\
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              C ` i
            ) = if (
              ( 1st ` ( A ` i ) ) = B ,
              <.
                ( 1st ` ( A ` i ) ) ,
                ( ( 2nd ` ( A ` i ) ) + 1 )
              >. ,
              ( A ` i )
            )
        )
      )
      \/
      (
        -.
        E. j e. ( 0 ..^ ( # ` A ) )
          ( 1st ` ( A ` j ) ) = B
        /\
        (
          ( # ` C ) = ( ( # ` A ) + 1 )
          /\
          (
            A. i e. ( 0 ..^ ( # ` A ) )
              ( C ` i ) = ( A ` i )
            /\
            ( C ` ( # ` A ) ) = <. B , 1 >.
          )
        )
      )
    )
  ) $.
$}

${
  $d i t A B $.

  verina76-frequency-list-graph-definition $a |- (
    VERINA76FrequencyListGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word VERINA76Pair
    )
    /\
    E. t e. Word ( Word VERINA76Pair )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = (/)
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              VERINA76FrequencyUpdateGraph
                ( t ` i )
                ( A ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina76-frequency-list-definition $a |- (
    VERINA76FrequencyList A
  ) = (
    iota_ y e. Word VERINA76Pair
      ( VERINA76FrequencyListGraph A y )
  ) $.
$}

${
  $d i p A B C $.

  verina76-insert-sorted-graph-definition $a |- (
    VERINA76InsertSortedGraph A B C
  ) <-> (
    (
      (
        A e. VERINA76Pair
        /\
        B e. Word VERINA76Pair
      )
      /\
      C e. Word VERINA76Pair
    )
    /\
    E. p e. NN0
      (
        p <_ ( # ` B )
        /\
        (
          (
            A. i e. ( 0 ..^ p )
              -. (
                ( 2nd ` ( B ` i ) ) < ( 2nd ` A )
              )
            /\
            (
              p < ( # ` B )
              ->
              ( 2nd ` ( B ` p ) ) < ( 2nd ` A )
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
                A. i e. ( 0 ..^ p )
                  ( C ` i ) = ( B ` i )
                /\
                A. i e. ( p ..^ ( # ` B ) )
                  ( C ` ( i + 1 ) ) = ( B ` i )
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d i t A B $.

  verina76-sorted-graph-definition $a |- (
    VERINA76SortedGraph A B
  ) <-> (
    (
      A e. Word VERINA76Pair
      /\
      B e. Word VERINA76Pair
    )
    /\
    E. t e. Word ( Word VERINA76Pair )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = (/)
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              VERINA76InsertSortedGraph
                ( A ` i )
                ( t ` i )
                ( t ` ( i + 1 ) )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina76-sorted-definition $a |- (
    VERINA76Sorted A
  ) = (
    iota_ y e. Word VERINA76Pair
      ( VERINA76SortedGraph A y )
  ) $.
$}

${
  $d i A B C $.

  verina76-take-keys-graph-definition $a |- (
    VERINA76TakeKeysGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA76Pair
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = (
        VERINA76NatMin B ( # ` A )
      )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        ( C ` i ) = ( 1st ` ( A ` i ) )
    )
  ) $.
$}

${
  $d y A B $.

  verina76-take-keys-definition $a |- (
    VERINA76TakeKeys A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA76TakeKeysGraph A B y )
  ) $.
$}

${
  $d f s A B C $.

  verina76-top-k-frequent-graph-definition $a |- (
    VERINA76TopKFrequentGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    E. f e. Word VERINA76Pair
      E. s e. Word VERINA76Pair
        (
          (
            VERINA76FrequencyListGraph A f
            /\
            VERINA76SortedGraph f s
          )
          /\
          VERINA76TakeKeysGraph s B C
        )
  ) $.
$}

${
  $d y A B $.

  verina76-top-k-frequent-definition $a |- (
    VERINA76TopKFrequent A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA76TopKFrequentGraph A B y )
  ) $.
$}

verina76-distinct-count-definition $a |- (
  VERINA76DistinctCount A
) = (
  # ` ran A
) $.

verina76-precondition-definition $a |- (
  VERINA76Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. NN0
  )
  /\
  B <_ ( VERINA76DistinctCount A )
) $.

${
  $d i j A B C $.

  verina76-postcondition-definition $a |- (
    VERINA76Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = B
      /\
      (
        ran C C_ ran A
        /\
        (
          A. i e. ( 0 ..^ ( # ` C ) )
            A. j e. ( 0 ..^ ( # ` C ) )
              (
                i < j
                ->
                ( C ` i ) =/= ( C ` j )
              )
          /\
          (
            A. i e. ( 0 ..^ ( # ` C ) )
              A. j e. ( 0 ..^ ( # ` A ) )
                (
                  ( A ` j ) e. ran C
                  \/
                  (
                    VERINA76Count A ( A ` j )
                  ) <_ (
                    VERINA76Count A ( C ` i )
                  )
                )
            /\
            A. i e. ( 0 ..^ ( # ` C ) )
              A. j e. ( 0 ..^ ( # ` C ) )
                (
                  i < j
                  ->
                  (
                    VERINA76Count A ( C ` j )
                  ) <_ (
                    VERINA76Count A ( C ` i )
                  )
                )
          )
        )
      )
    )
  ) $.
$}

${
  $d k w $.

  verina-advanced-76-top-k-frequent $a |- A. w e. Word ZZ
    A. k e. NN0
      (
        ( VERINA76Pre w k )
        ->
        (
          VERINA76Post
            w
            k
            ( VERINA76TopKFrequent w k )
        )
      )
  $.
$}
