$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_22
  (verina__metamath__verina_basic_22), catalog title dissimilarElements: the
  exact two-pass hash-set computation returns the sorted duplicate-free
  symmetric difference of two arbitrary finite integer arrays and satisfies
  its complete correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer arrays and lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, ran w is its entry set,
  and 0 ..^ ( # ` w ) is its complete valid-index set. Booleans are represented
  by zero and one.

  VERINAB22InArray is the source helper a.any (fun y => y = x), represented
  by its exact Boolean membership value. A hash set is represented
  extensionally by a duplicate-free integer word. VERINAB22HashInsert keeps
  that word when the value is already present and otherwise prepends the new
  value, which has exactly the source Std.HashSet.insert membership semantics.
  VERINAB22FoldGraph records every state of the source left-to-right fold:
  values present in the other array leave the accumulator unchanged, and all
  other values are inserted. The initial emptyWithCapacity set is the empty
  word. Capacity and bucket layout are unobservable.

  VERINAB22ToList chooses the canonical word representative of the final hash
  set. The source HashSet.toList can differ from this representative only by
  a permutation. VERINAB22MergeSortGraph characterizes the unique
  nondecreasing word with the same integer multiplicities, so sorting either
  representative gives exactly the same result as the source
  List.mergeSort (fun x y => x <= y). VERINAB22DissimilarElements composes
  the first fold over a against b, the second fold over b against a, toList,
  and mergeSort. Its output is therefore fixed by the executable computation
  independently of the postcondition.

  VERINAB22Pre is the source True precondition on the two typed Array Int
  inputs. VERINAB22PairwiseLE and VERINAB22Nodup reproduce List.Pairwise
  (fun x y => x <= y) and List.Nodup. VERINAB22Post preserves all five source
  conjuncts: every result entry has unequal inArray Booleans, the result is
  nondecreasing and duplicate-free, and each occurrence in either input is
  included exactly when it is absent from the other input. The proof-valued
  precondition argument is computationally and propositionally unused and is
  represented by the explicit antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB22InArray
  VERINAB22HashInsert
  VERINAB22FoldGraph VERINAB22Fold
  VERINAB22ToList
  VERINAB22MergeSortGraph VERINAB22MergeSort
  VERINAB22Pre VERINAB22DissimilarElements
  VERINAB22PairwiseLE VERINAB22Nodup VERINAB22Post
$.

verinab22-in-array-syntax
  $a class ( VERINAB22InArray A B ) $.
verinab22-hash-insert-syntax
  $a class ( VERINAB22HashInsert A B ) $.
verinab22-fold-graph-syntax
  $a wff ( VERINAB22FoldGraph A B C D ) $.
verinab22-fold-syntax
  $a class ( VERINAB22Fold A B C ) $.
verinab22-to-list-syntax
  $a class ( VERINAB22ToList A ) $.
verinab22-merge-sort-graph-syntax
  $a wff ( VERINAB22MergeSortGraph A B ) $.
verinab22-merge-sort-syntax
  $a class ( VERINAB22MergeSort A ) $.
verinab22-precondition-syntax
  $a wff ( VERINAB22Pre A B ) $.
verinab22-program-syntax
  $a class ( VERINAB22DissimilarElements A B ) $.
verinab22-pairwise-le-syntax
  $a wff ( VERINAB22PairwiseLE A ) $.
verinab22-nodup-syntax
  $a wff ( VERINAB22Nodup A ) $.
verinab22-postcondition-syntax
  $a wff ( VERINAB22Post A B C ) $.

verinab22-in-array-definition $a |- (
  VERINAB22InArray A B
) = if (
  B e. ran A ,
  1 ,
  0
) $.

verinab22-hash-insert-definition $a |- (
  VERINAB22HashInsert A B
) = if (
  B e. ran A ,
  A ,
  ( <" B "> ++ A )
) $.

${
  $d k t A B C D $.

  verinab22-fold-graph-definition $a |- (
    VERINAB22FoldGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. Word ZZ
        )
        /\
        C e. Word ZZ
      )
      /\
      D e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = C
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              t ` ( k + 1 )
            ) = if (
              (
                VERINAB22InArray
                  B
                  ( A ` k )
              ) = 1 ,
              ( t ` k ) ,
              (
                VERINAB22HashInsert
                  ( t ` k )
                  ( A ` k )
              )
            )
          /\
          D = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab22-fold-definition $a |- (
    VERINAB22Fold A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB22FoldGraph A B C y )
  ) $.
$}

verinab22-to-list-definition $a |- (
  VERINAB22ToList A
) = A $.

${
  $d i j x A B $.

  verinab22-merge-sort-graph-definition $a |- (
    VERINAB22MergeSortGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` B ) )
        A. j e. ( 0 ..^ ( # ` B ) )
          (
            i < j
            ->
            ( B ` i ) <_ ( B ` j )
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

  verinab22-merge-sort-definition $a |- (
    VERINAB22MergeSort A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB22MergeSortGraph A y )
  ) $.
$}

verinab22-precondition-definition $a |- (
  VERINAB22Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. Word ZZ
) $.

verinab22-program-definition $a |- (
  VERINAB22DissimilarElements A B
) = (
  VERINAB22MergeSort
    (
      VERINAB22ToList
        (
          VERINAB22Fold
            B
            A
            (
              VERINAB22Fold
                A
                B
                (/)
            )
        )
    )
) $.

${
  $d i j A $.

  verinab22-pairwise-le-definition $a |- (
    VERINAB22PairwiseLE A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) <_ ( A ` j )
        )
  ) $.
$}

${
  $d i j A $.

  verinab22-nodup-definition $a |- (
    VERINAB22Nodup A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i =/= j
          ->
          ( A ` i ) =/= ( A ` j )
        )
  ) $.
$}

${
  $d i A B C $.

  verinab22-postcondition-definition $a |- (
    VERINAB22Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` C ) )
        (
          VERINAB22InArray
            A
            ( C ` i )
        ) =/= (
          VERINAB22InArray
            B
            ( C ` i )
        )
      /\
      (
        ( VERINAB22PairwiseLE C )
        /\
        (
          ( VERINAB22Nodup C )
          /\
          (
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                (
                  ( A ` i ) e. ran B
                  ->
                  ( A ` i ) e/ ran C
                )
                /\
                (
                  ( A ` i ) e/ ran B
                  ->
                  ( A ` i ) e. ran C
                )
              )
            /\
            A. i e. ( 0 ..^ ( # ` B ) )
              (
                (
                  ( B ` i ) e. ran A
                  ->
                  ( B ` i ) e/ ran C
                )
                /\
                (
                  ( B ` i ) e/ ran A
                  ->
                  ( B ` i ) e. ran C
                )
              )
          )
        )
      )
    )
  ) $.
$}

verina-basic-22-dissimilar-elements $a |- A. a e. Word ZZ
  A. b e. Word ZZ
    (
      ( VERINAB22Pre a b )
      ->
      (
        VERINAB22Post
          a
          b
          ( VERINAB22DissimilarElements a b )
      )
    )
$.
