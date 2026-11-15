$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_104 (verina__metamath__verina_basic_104), catalog title
  update_map: the exact list-backed integer-map insertion fold and stable
  key-sorting computation satisfies its unique-key, lookup, value-selection,
  and sortedness correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB104Pair is Int x Int, VERINAB104Map is the source Map structure's
  entries field represented by an arbitrary finite word of integer pairs, and
  VERINAB104Empty is the source empty map. For a word w, # ` w is its length,
  w ` i is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINAB104KeepCount counts entries before a specified index whose key is
  different from the inserted key. VERINAB104FilterKeyGraph therefore gives
  exactly the stable List.filter used by insert. VERINAB104InsertGraph copies
  that filtered word and appends the new key-value pair. The fold graph threads
  this exact insertion through m2 from left to right, starting at m1.

  VERINAB104MergeSortGraph uses a permutation of source indices ordered first
  by key and then by original index. This is exactly stable List.mergeSort
  with comparator fun a b => a.1 <= b.1, including equal-key tie ordering.
  VERINAB104UpdateMapGraph composes the insertion fold and that sort, so the
  executable result is fixed independently of the postcondition.

  VERINAB104FindGraph is List.find? with integer key equality: it returns the
  value at the least matching index, or none when no key matches.
  VERINAB104NodupKeys is List.Nodup after mapping first projections, and
  VERINAB104Pre is the conjunction of that condition for both source maps.
  VERINAB104PairwiseLE is List.Pairwise on nondecreasing keys.
  VERINAB104Post preserves all four source conjuncts: sorted output; every m2
  entry has its value in the result; every m1 entry not overridden by m2 keeps
  its value; and each result entry has exactly the branch-selected value from
  m1 and m2.

  The source proof-valued precondition argument does not affect computation
  and is not inspected by the postcondition, so the final correctness
  assertion represents it by an explicit antecedent. The source Map BEq
  instance is unused by every preserved computation and proposition. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB104Pair VERINAB104Map VERINAB104Empty
  VERINAB104KeepCount
  VERINAB104FilterKeyGraph VERINAB104FilterKey
  VERINAB104InsertGraph VERINAB104Insert
  VERINAB104FoldGraph VERINAB104Fold
  VERINAB104MergeSortGraph VERINAB104MergeSort
  VERINAB104UpdateMapGraph VERINAB104UpdateMap
  VERINAB104None VERINAB104Some VERINAB104OptionInt
  VERINAB104FindGraph VERINAB104Find
  VERINAB104NodupKeys VERINAB104Pre
  VERINAB104PairwiseLE VERINAB104Post
$.

verinab104-pair-syntax
  $a class VERINAB104Pair $.
verinab104-map-syntax
  $a class VERINAB104Map $.
verinab104-empty-syntax
  $a class VERINAB104Empty $.
verinab104-keep-count-syntax
  $a class ( VERINAB104KeepCount A B C ) $.
verinab104-filter-key-graph-syntax
  $a wff ( VERINAB104FilterKeyGraph A B C ) $.
verinab104-filter-key-syntax
  $a class ( VERINAB104FilterKey A B ) $.
verinab104-insert-graph-syntax
  $a wff ( VERINAB104InsertGraph A B C D ) $.
verinab104-insert-syntax
  $a class ( VERINAB104Insert A B C ) $.
verinab104-fold-graph-syntax
  $a wff ( VERINAB104FoldGraph A B C ) $.
verinab104-fold-syntax
  $a class ( VERINAB104Fold A B ) $.
verinab104-merge-sort-graph-syntax
  $a wff ( VERINAB104MergeSortGraph A B ) $.
verinab104-merge-sort-syntax
  $a class ( VERINAB104MergeSort A ) $.
verinab104-update-map-graph-syntax
  $a wff ( VERINAB104UpdateMapGraph A B C ) $.
verinab104-update-map-syntax
  $a class ( VERINAB104UpdateMap A B ) $.
verinab104-none-syntax
  $a class VERINAB104None $.
verinab104-some-syntax
  $a class ( VERINAB104Some A ) $.
verinab104-option-int-syntax
  $a class VERINAB104OptionInt $.
verinab104-find-graph-syntax
  $a wff ( VERINAB104FindGraph A B C ) $.
verinab104-find-syntax
  $a class ( VERINAB104Find A B ) $.
verinab104-nodup-keys-syntax
  $a wff ( VERINAB104NodupKeys A ) $.
verinab104-precondition-syntax
  $a wff ( VERINAB104Pre A B ) $.
verinab104-pairwise-le-syntax
  $a wff ( VERINAB104PairwiseLE A ) $.
verinab104-postcondition-syntax
  $a wff ( VERINAB104Post A B C ) $.

verinab104-pair-definition $a |- VERINAB104Pair = (
  ZZ X. ZZ
) $.

verinab104-map-definition $a |- VERINAB104Map = (
  Word VERINAB104Pair
) $.

verinab104-empty-definition $a |- VERINAB104Empty = (/) $.

${
  $d i A B C $.

  verinab104-keep-count-definition $a |- (
    VERINAB104KeepCount A B C
  ) = (
    # ` {
      i e. ( 0 ..^ C )
      |
      ( 1st ` ( A ` i ) ) =/= B
    }
  ) $.
$}

${
  $d i A B C $.

  verinab104-filter-key-graph-definition $a |- (
    VERINAB104FilterKeyGraph A B C
  ) <-> (
    (
      (
        A e. VERINAB104Map
        /\
        B e. ZZ
      )
      /\
      C e. VERINAB104Map
    )
    /\
    (
      ( # ` C ) = (
        VERINAB104KeepCount A B ( # ` A )
      )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          ( 1st ` ( A ` i ) ) =/= B
          ->
          (
            C ` ( VERINAB104KeepCount A B i )
          ) = ( A ` i )
        )
    )
  ) $.
$}

${
  $d y A B $.

  verinab104-filter-key-definition $a |- (
    VERINAB104FilterKey A B
  ) = (
    iota_ y e. VERINAB104Map
      ( VERINAB104FilterKeyGraph A B y )
  ) $.
$}

${
  $d i A B C D $.

  verinab104-insert-graph-definition $a |- (
    VERINAB104InsertGraph A B C D
  ) <-> (
    (
      (
        (
          A e. VERINAB104Map
          /\
          B e. ZZ
        )
        /\
        C e. ZZ
      )
      /\
      D e. VERINAB104Map
    )
    /\
    (
      ( # ` D ) = (
        ( # ` ( VERINAB104FilterKey A B ) ) + 1
      )
      /\
      (
        A. i e. (
          0 ..^ ( # ` ( VERINAB104FilterKey A B ) )
        )
          ( D ` i ) = (
            ( VERINAB104FilterKey A B ) ` i
          )
        /\
        (
          D ` ( # ` ( VERINAB104FilterKey A B ) )
        ) = <. B , C >.
      )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab104-insert-definition $a |- (
    VERINAB104Insert A B C
  ) = (
    iota_ y e. VERINAB104Map
      ( VERINAB104InsertGraph A B C y )
  ) $.
$}

${
  $d i t A B C $.

  verinab104-fold-graph-definition $a |- (
    VERINAB104FoldGraph A B C
  ) <-> (
    (
      (
        A e. VERINAB104Map
        /\
        B e. VERINAB104Map
      )
      /\
      C e. VERINAB104Map
    )
    /\
    E. t e. Word VERINAB104Map
      (
        (
          ( # ` t ) = ( ( # ` B ) + 1 )
          /\
          ( t ` 0 ) = A
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` B ) )
            (
              VERINAB104InsertGraph
                ( t ` i )
                ( 1st ` ( B ` i ) )
                ( 2nd ` ( B ` i ) )
                ( t ` ( i + 1 ) )
            )
          /\
          C = ( t ` ( # ` B ) )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab104-fold-definition $a |- (
    VERINAB104Fold A B
  ) = (
    iota_ y e. VERINAB104Map
      ( VERINAB104FoldGraph A B y )
  ) $.
$}

${
  $d i j p A B $.

  verinab104-merge-sort-graph-definition $a |- (
    VERINAB104MergeSortGraph A B
  ) <-> (
    (
      A e. VERINAB104Map
      /\
      B e. VERINAB104Map
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

  verinab104-merge-sort-definition $a |- (
    VERINAB104MergeSort A
  ) = (
    iota_ y e. VERINAB104Map
      ( VERINAB104MergeSortGraph A y )
  ) $.
$}

${
  $d f A B C $.

  verinab104-update-map-graph-definition $a |- (
    VERINAB104UpdateMapGraph A B C
  ) <-> (
    (
      (
        A e. VERINAB104Map
        /\
        B e. VERINAB104Map
      )
      /\
      C e. VERINAB104Map
    )
    /\
    E. f e. VERINAB104Map
      (
        VERINAB104FoldGraph A B f
        /\
        VERINAB104MergeSortGraph f C
      )
  ) $.
$}

${
  $d y A B $.

  verinab104-update-map-definition $a |- (
    VERINAB104UpdateMap A B
  ) = (
    iota_ y e. VERINAB104Map
      ( VERINAB104UpdateMapGraph A B y )
  ) $.
$}

verinab104-none-definition $a |- VERINAB104None = (/) $.

verinab104-some-definition $a |- (
  VERINAB104Some A
) = <. 1 , A >. $.

${
  $d x z $.

  verinab104-option-int-definition $a |- VERINAB104OptionInt = {
    x |
    (
      x = VERINAB104None
      \/
      E. z e. ZZ x = ( VERINAB104Some z )
    )
  } $.
$}

${
  $d i j A B C $.

  verinab104-find-graph-definition $a |- (
    VERINAB104FindGraph A B C
  ) <-> (
    (
      (
        A e. VERINAB104Map
        /\
        B e. ZZ
      )
      /\
      C e. VERINAB104OptionInt
    )
    /\
    (
      E. i e. ( 0 ..^ ( # ` A ) )
        (
          (
            ( 1st ` ( A ` i ) ) = B
            /\
            A. j e. ( 0 ..^ i )
              ( 1st ` ( A ` j ) ) =/= B
          )
          /\
          C = (
            VERINAB104Some ( 2nd ` ( A ` i ) )
          )
        )
      \/
      (
        -.
        E. i e. ( 0 ..^ ( # ` A ) )
          ( 1st ` ( A ` i ) ) = B
        /\
        C = VERINAB104None
      )
    )
  ) $.
$}

${
  $d y A B $.

  verinab104-find-definition $a |- (
    VERINAB104Find A B
  ) = (
    iota_ y e. VERINAB104OptionInt
      ( VERINAB104FindGraph A B y )
  ) $.
$}

${
  $d i j A $.

  verinab104-nodup-keys-definition $a |- (
    VERINAB104NodupKeys A
  ) <-> (
    A e. VERINAB104Map
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          (
            1st ` ( A ` i )
          ) =/= (
            1st ` ( A ` j )
          )
        )
  ) $.
$}

verinab104-precondition-definition $a |- (
  VERINAB104Pre A B
) <-> (
  ( VERINAB104NodupKeys A )
  /\
  ( VERINAB104NodupKeys B )
) $.

${
  $d i j A $.

  verinab104-pairwise-le-definition $a |- (
    VERINAB104PairwiseLE A
  ) <-> (
    A e. VERINAB104Map
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          (
            1st ` ( A ` i )
          ) <_ (
            1st ` ( A ` j )
          )
        )
  ) $.
$}

${
  $d i u v A B C $.

  verinab104-postcondition-definition $a |- (
    VERINAB104Post A B C
  ) <-> (
    (
      (
        A e. VERINAB104Map
        /\
        B e. VERINAB104Map
      )
      /\
      C e. VERINAB104Map
    )
    /\
    (
      ( VERINAB104PairwiseLE C )
      /\
      (
        A. i e. ( 0 ..^ ( # ` B ) )
          (
            VERINAB104Find
              C
              ( 1st ` ( B ` i ) )
          ) = (
            VERINAB104Some ( 2nd ` ( B ` i ) )
          )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              (
                VERINAB104Find
                  B
                  ( 1st ` ( A ` i ) )
              ) = VERINAB104None
              ->
              (
                VERINAB104Find
                  C
                  ( 1st ` ( A ` i ) )
              ) = (
                VERINAB104Some ( 2nd ` ( A ` i ) )
              )
            )
          /\
          A. i e. ( 0 ..^ ( # ` C ) )
            (
              E. u e. ZZ
                (
                  (
                    VERINAB104Find
                      A
                      ( 1st ` ( C ` i ) )
                  ) = ( VERINAB104Some u )
                  /\
                  (
                    E. v e. ZZ
                      (
                        (
                          VERINAB104Find
                            B
                            ( 1st ` ( C ` i ) )
                        ) = ( VERINAB104Some v )
                        /\
                        ( 2nd ` ( C ` i ) ) = v
                      )
                    \/
                    (
                      (
                        VERINAB104Find
                          B
                          ( 1st ` ( C ` i ) )
                      ) = VERINAB104None
                      /\
                      ( 2nd ` ( C ` i ) ) = u
                    )
                  )
                )
              \/
              (
                (
                  VERINAB104Find
                    A
                    ( 1st ` ( C ` i ) )
                ) = VERINAB104None
                /\
                (
                  VERINAB104Find
                    B
                    ( 1st ` ( C ` i ) )
                ) = (
                  VERINAB104Some ( 2nd ` ( C ` i ) )
                )
              )
            )
        )
      )
    )
  ) $.
$}

${
  $d m n $.

  verina-basic-104-update-map $a |- A. m e. VERINAB104Map
    A. n e. VERINAB104Map
      (
        ( VERINAB104Pre m n )
        ->
        (
          VERINAB104Post
            m
            n
            ( VERINAB104UpdateMap m n )
        )
      )
  $.
$}
