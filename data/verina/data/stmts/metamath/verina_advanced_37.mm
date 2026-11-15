$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_37 (verina__metamath__verina_advanced_37), catalog title
  majorityElement: exact recursive insertion sorting followed by middle-index
  lookup returns the majority integer of an arbitrary nonempty finite integer
  list satisfying the stated majority-existence precondition and correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set. VERINA37Count is List.count,
  and VERINA37Half is Lean natural-number division by two.

  VERINA37InsertGraph gives the exact computation of the local insert
  recursion. Its position p is the first input position whose value is at
  least the inserted integer, or the word length when there is no such
  position. The output copies the prefix, places the new integer at p, and
  shifts the remaining suffix by one. VERINA37Insert selects the unique word
  described by this graph.

  VERINA37SortGraph gives the exact computation of the local insertionSort
  recursion. Its trace begins with the empty word and inserts the input
  entries from right to left, matching
  insertionSort (h :: t) = insert h (insertionSort t).
  VERINA37InsertionSort selects the unique final trace value.

  VERINA37GetAt is exactly the local getAt helper: it returns the entry at a
  natural index when that index is in range and returns integer zero
  otherwise, matching the head of List.drop with the source default.
  VERINA37MajorityElement sorts the input, computes half of the sorted
  length, and applies that helper, exactly preserving the executable source
  program rather than selecting an output from the postcondition.

  VERINA37Pre is exactly positive length together with List.any of a value
  whose count exceeds floor(length / 2). VERINA37Post is exactly the strict
  majority bound for the result and List.all of the source disjunction for
  every input entry. The proof-valued precondition argument is
  computationally and propositionally unused and is omitted from the target
  function and postcondition. The final $a declaration is the source
  correctness proposition. Every earlier $a is syntax or a faithful
  definition, and this database has no $p declaration.
$)

$c
  VERINA37Count VERINA37Half
  VERINA37InsertGraph VERINA37Insert
  VERINA37SortGraph VERINA37InsertionSort
  VERINA37GetAt VERINA37MajorityElement
  VERINA37Pre VERINA37Post
$.

verina37-count-syntax
  $a class ( VERINA37Count A B ) $.
verina37-half-syntax
  $a class ( VERINA37Half A ) $.
verina37-insert-graph-syntax
  $a wff ( VERINA37InsertGraph A B C ) $.
verina37-insert-syntax
  $a class ( VERINA37Insert A B ) $.
verina37-sort-graph-syntax
  $a wff ( VERINA37SortGraph A B ) $.
verina37-insertion-sort-syntax
  $a class ( VERINA37InsertionSort A ) $.
verina37-get-at-syntax
  $a class ( VERINA37GetAt A B ) $.
verina37-majority-element-syntax
  $a class ( VERINA37MajorityElement A ) $.
verina37-precondition-syntax
  $a wff ( VERINA37Pre A ) $.
verina37-postcondition-syntax
  $a wff ( VERINA37Post A B ) $.

${
  $d i A B $.

  verina37-count-definition $a |- (
    VERINA37Count A B
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( A ` i ) = B
    }
  ) $.
$}

verina37-half-definition $a |- (
  VERINA37Half A
) = (
  |_ ` ( ( # ` A ) / 2 )
) $.

${
  $d j p A B C $.

  verina37-insert-graph-definition $a |- (
    VERINA37InsertGraph A B C
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

  verina37-insert-definition $a |- (
    VERINA37Insert A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA37InsertGraph A B y )
  ) $.
$}

${
  $d k t A B $.

  verina37-sort-graph-definition $a |- (
    VERINA37SortGraph A B
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
              VERINA37InsertGraph
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

  verina37-insertion-sort-definition $a |- (
    VERINA37InsertionSort A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA37SortGraph A y )
  ) $.
$}

verina37-get-at-definition $a |- (
  VERINA37GetAt A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verina37-majority-element-definition $a |- (
  VERINA37MajorityElement A
) = (
  VERINA37GetAt
    ( VERINA37InsertionSort A )
    ( VERINA37Half ( VERINA37InsertionSort A ) )
) $.

${
  $d i A $.

  verina37-precondition-definition $a |- (
    VERINA37Pre A
  ) <-> (
    (
      A e. Word ZZ
      /\
      0 < ( # ` A )
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      (
        VERINA37Half A
      ) < (
        VERINA37Count A ( A ` i )
      )
  ) $.
$}

${
  $d i A B $.

  verina37-postcondition-definition $a |- (
    VERINA37Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      (
        VERINA37Half A
      ) < (
        VERINA37Count A B
      )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          ( A ` i ) = B
          \/
          (
            VERINA37Count A ( A ` i )
          ) <_ (
            VERINA37Half A
          )
        )
    )
  ) $.
$}

verina-advanced-37-majority-element
  $a |- A. w e. Word ZZ
    (
      ( VERINA37Pre w )
      ->
      (
        VERINA37Post
          w
          ( VERINA37MajorityElement w )
      )
    )
  $.
