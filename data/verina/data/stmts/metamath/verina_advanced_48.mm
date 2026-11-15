$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_48 (verina__metamath__verina_advanced_48), catalog title
  mergeSort: the exact executable recursive insertion-sort implementation on
  an arbitrary finite integer list returns a nondecreasing permutation of
  that list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its length, w ` k
  is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA48InsertGraph gives the exact computation of the source local insert
  recursion. Its position p is the first input position whose value is at
  least the inserted integer, or the word length if there is no such
  position. The output copies the prefix, places the new integer at p, and
  shifts the remaining suffix by one. VERINA48Insert selects the unique word
  described by this graph.

  VERINA48SortGraph gives the exact computation of the source local sort
  recursion. Its trace begins with the empty word and inserts the input
  entries from right to left, matching sort (x :: xs) = insert x (sort xs).
  VERINA48Sort selects the unique final trace value, and VERINA48MergeSort is
  the source executable implementation (which uses insertion sort despite
  its mergeSort name). Thus the implementation is not an unconstrained
  function and is not selected from the postcondition.

  VERINA48Pre is the source True precondition together with the List Int
  input type. VERINA48Pairwise is List.Pairwise with integer <=, and
  VERINA48Perm is List.isPerm, represented by equality of the multiplicity
  of every integer. VERINA48Post is their conjunction. The proof-valued
  precondition argument is computationally and propositionally unused and
  is omitted from the target function and postcondition. The final $a
  declaration is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA48InsertGraph VERINA48Insert
  VERINA48SortGraph VERINA48Sort VERINA48MergeSort
  VERINA48Pre VERINA48Pairwise VERINA48Perm VERINA48Post
$.

verina48-insert-graph-syntax
  $a wff ( VERINA48InsertGraph A B C ) $.
verina48-insert-syntax
  $a class ( VERINA48Insert A B ) $.
verina48-sort-graph-syntax
  $a wff ( VERINA48SortGraph A B ) $.
verina48-sort-syntax
  $a class ( VERINA48Sort A ) $.
verina48-merge-sort-syntax
  $a class ( VERINA48MergeSort A ) $.
verina48-precondition-syntax
  $a wff ( VERINA48Pre A ) $.
verina48-pairwise-syntax
  $a wff ( VERINA48Pairwise A ) $.
verina48-permutation-syntax
  $a wff ( VERINA48Perm A B ) $.
verina48-postcondition-syntax
  $a wff ( VERINA48Post A B ) $.

${
  $d j p A B C $.

  verina48-insert-graph-definition $a |- (
    VERINA48InsertGraph A B C
  ) <-> (
    (
      (
        A e. ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    E. p e. NN0
      (
        p <_ ( # ` B )
        /\
        (
          (
            A. j e. ( 0 ..^ p )
              -. A <_ ( B ` j )
            /\
            (
              p < ( # ` B )
              ->
              A <_ ( B ` p )
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

  verina48-insert-definition $a |- (
    VERINA48Insert A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA48InsertGraph A B y )
  ) $.
$}

${
  $d k t A B $.

  verina48-sort-graph-definition $a |- (
    VERINA48SortGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
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
              VERINA48InsertGraph
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

  verina48-sort-definition $a |- (
    VERINA48Sort A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA48SortGraph A y )
  ) $.
$}

verina48-merge-sort-definition $a |- (
  VERINA48MergeSort A
) = (
  VERINA48Sort A
) $.

verina48-precondition-definition $a |- (
  VERINA48Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d i j A $.

  verina48-pairwise-definition $a |- (
    VERINA48Pairwise A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( A ` i ) <_ ( A ` j )
          )
    )
  ) $.
$}

${
  $d i j x A B $.

  verina48-permutation-definition $a |- (
    VERINA48Perm A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
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
  ) $.
$}

verina48-postcondition-definition $a |- (
  VERINA48Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    ( VERINA48Pairwise B )
    /\
    ( VERINA48Perm A B )
  )
) $.

verina-advanced-48-merge-sort $a |- A. w e. Word ZZ
  (
    ( VERINA48Pre w )
    ->
    (
      VERINA48Post
        w
        ( VERINA48MergeSort w )
    )
  )
$.
