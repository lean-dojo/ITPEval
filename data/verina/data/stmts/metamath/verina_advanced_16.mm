$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_16, catalog title insertionSort: exact recursive insertion
  sort on an arbitrary finite integer list returns a nondecreasing
  permutation of that list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its length, w ` k
  is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA16InsertGraph gives the exact computation of the source local insert
  recursion. Its position p is the first input position whose value is at
  least the inserted integer, or the word length if there is no such
  position. The output copies the prefix, places the new integer at p, and
  shifts the remaining suffix by one. VERINA16Insert selects the unique word
  described by this graph.

  VERINA16SortGraph gives the exact computation of the source local sort
  recursion. Its trace begins with the empty word and inserts the input
  entries from right to left, matching sort (x :: xs) = insert x (sort xs).
  VERINA16Sort selects the unique final trace value, and
  VERINA16InsertionSort is the source executable implementation. Thus the
  implementation is not an unconstrained function and is not selected from
  the postcondition.

  VERINA16Pre is the source True precondition together with the List Int
  input type. VERINA16Pairwise is List.Pairwise with integer <=, and
  VERINA16Perm
  is List.isPerm, represented by equality of the multiplicity of every
  integer. VERINA16Post is their conjunction. The proof-valued precondition
  argument is computationally unused and is omitted from the target
  function. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database has
  no $p declaration.
$)

$c
  VERINA16InsertGraph VERINA16Insert
  VERINA16SortGraph VERINA16Sort VERINA16InsertionSort
  VERINA16Pre VERINA16Pairwise VERINA16Perm VERINA16Post
$.

verina16-insert-graph-syntax
  $a wff ( VERINA16InsertGraph A B C ) $.
verina16-insert-syntax
  $a class ( VERINA16Insert A B ) $.
verina16-sort-graph-syntax
  $a wff ( VERINA16SortGraph A B ) $.
verina16-sort-syntax
  $a class ( VERINA16Sort A ) $.
verina16-insertion-sort-syntax
  $a class ( VERINA16InsertionSort A ) $.
verina16-precondition-syntax
  $a wff ( VERINA16Pre A ) $.
verina16-pairwise-syntax
  $a wff ( VERINA16Pairwise A ) $.
verina16-permutation-syntax
  $a wff ( VERINA16Perm A B ) $.
verina16-postcondition-syntax
  $a wff ( VERINA16Post A B ) $.

${
  $d j p A B C $.

  verina16-insert-graph-definition $a |- (
    VERINA16InsertGraph A B C
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

  verina16-insert-definition $a |- (
    VERINA16Insert A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA16InsertGraph A B y )
  ) $.
$}

${
  $d k t A B $.

  verina16-sort-graph-definition $a |- (
    VERINA16SortGraph A B
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
              VERINA16InsertGraph
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

  verina16-sort-definition $a |- (
    VERINA16Sort A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA16SortGraph A y )
  ) $.
$}

verina16-insertion-sort-definition $a |- (
  VERINA16InsertionSort A
) = (
  VERINA16Sort A
) $.

verina16-precondition-definition $a |- (
  VERINA16Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d i j A $.

  verina16-pairwise-definition $a |- (
    VERINA16Pairwise A
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

  verina16-permutation-definition $a |- (
    VERINA16Perm A B
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

verina16-postcondition-definition $a |- (
  VERINA16Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    ( VERINA16Pairwise B )
    /\
    ( VERINA16Perm A B )
  )
) $.

verina-advanced-16-insertion-sort $a |- A. w e. Word ZZ
  (
    ( VERINA16Pre w )
    ->
    (
      VERINA16Post
        w
        ( VERINA16InsertionSort w )
    )
  )
$.
