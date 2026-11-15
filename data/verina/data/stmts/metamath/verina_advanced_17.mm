$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_17, catalog title insertionSort: exact recursive insertion
  sort on an arbitrary finite integer list returns a nondecreasing
  permutation of that list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its length, w ` k
  is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA17InsertGraph gives the exact computation of the source insertElement
  recursion. Its position p is the first input position whose value is at
  least the inserted integer, or the word length if there is no such
  position. The output copies the prefix, places the new integer at p, and
  shifts the remaining suffix by one. VERINA17Insert selects the unique word
  described by this graph.

  VERINA17SortGraph gives the exact computation of the source sortList
  recursion. Its trace begins with the empty word and inserts the input
  entries from right to left, matching
  sortList (x :: xs) = insertElement x (sortList xs).
  VERINA17Sort selects the unique final trace value, and
  VERINA17InsertionSort is the source executable implementation. Thus the
  implementation is not an unconstrained function and is not selected from
  the postcondition.

  VERINA17Pre is the source True precondition together with the List Int
  input type. VERINA17Pairwise is List.Pairwise with integer <=, and
  VERINA17Perm is List.isPerm, represented by equality of the multiplicity
  of every integer. VERINA17Post is their conjunction. The proof-valued
  precondition argument is computationally unused and is omitted from the
  target function. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and this
  database has no $p declaration.
$)

$c
  VERINA17InsertGraph VERINA17Insert
  VERINA17SortGraph VERINA17Sort VERINA17InsertionSort
  VERINA17Pre VERINA17Pairwise VERINA17Perm VERINA17Post
$.

verina17-insert-graph-syntax
  $a wff ( VERINA17InsertGraph A B C ) $.
verina17-insert-syntax
  $a class ( VERINA17Insert A B ) $.
verina17-sort-graph-syntax
  $a wff ( VERINA17SortGraph A B ) $.
verina17-sort-syntax
  $a class ( VERINA17Sort A ) $.
verina17-insertion-sort-syntax
  $a class ( VERINA17InsertionSort A ) $.
verina17-precondition-syntax
  $a wff ( VERINA17Pre A ) $.
verina17-pairwise-syntax
  $a wff ( VERINA17Pairwise A ) $.
verina17-permutation-syntax
  $a wff ( VERINA17Perm A B ) $.
verina17-postcondition-syntax
  $a wff ( VERINA17Post A B ) $.

${
  $d j p A B C $.

  verina17-insert-graph-definition $a |- (
    VERINA17InsertGraph A B C
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

  verina17-insert-definition $a |- (
    VERINA17Insert A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA17InsertGraph A B y )
  ) $.
$}

${
  $d k t A B $.

  verina17-sort-graph-definition $a |- (
    VERINA17SortGraph A B
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
              VERINA17InsertGraph
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

  verina17-sort-definition $a |- (
    VERINA17Sort A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA17SortGraph A y )
  ) $.
$}

verina17-insertion-sort-definition $a |- (
  VERINA17InsertionSort A
) = (
  VERINA17Sort A
) $.

verina17-precondition-definition $a |- (
  VERINA17Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d i j A $.

  verina17-pairwise-definition $a |- (
    VERINA17Pairwise A
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

  verina17-permutation-definition $a |- (
    VERINA17Perm A B
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

verina17-postcondition-definition $a |- (
  VERINA17Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    ( VERINA17Pairwise B )
    /\
    ( VERINA17Perm A B )
  )
) $.

verina-advanced-17-insertion-sort $a |- A. w e. Word ZZ
  (
    ( VERINA17Pre w )
    ->
    (
      VERINA17Post
        w
        ( VERINA17InsertionSort w )
    )
  )
$.
