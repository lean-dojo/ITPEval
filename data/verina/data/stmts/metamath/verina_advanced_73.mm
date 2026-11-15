$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_73 (verina__metamath__verina_advanced_73), catalog title
  smallestMissing: the exact recursive scan of a strictly increasing finite
  natural-number list returns its least absent natural number, together with
  the complete precondition and postcondition correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` k is zero-based lookup, ran w is its membership
  set, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA73SortedList is the source sortedList let-binding and is extensionally
  the identity. VERINA73SearchGraph gives the exact computation of the local
  recursive search for arbitrary list and candidate arguments. Its trace
  starts at the supplied candidate. At every consumed position, an equal head
  increments the candidate, a smaller head leaves it unchanged, and a greater
  head stops the computation before that position. The trace also stops at
  list exhaustion. VERINA73Search selects the unique returned natural number,
  and VERINA73SmallestMissing invokes it on the source list with candidate
  zero. Thus the program output is fixed independently of the postcondition,
  and the operational graph permits no extra results.

  VERINA73Pre is exactly List.Pairwise (<) on the typed natural-number list.
  VERINA73Post says that the result is absent from the list and every smaller
  natural number is present. The proof-valued precondition arguments of the
  source program and postcondition are computationally and propositionally
  unused; they are represented by the explicit precondition antecedent of the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINA73SortedList
  VERINA73SearchGraph VERINA73Search
  VERINA73Pre VERINA73SmallestMissing VERINA73Post
$.

verina73-sorted-list-syntax
  $a class ( VERINA73SortedList A ) $.
verina73-search-graph-syntax
  $a wff ( VERINA73SearchGraph A B C ) $.
verina73-search-syntax
  $a class ( VERINA73Search A B ) $.
verina73-precondition-syntax
  $a wff ( VERINA73Pre A ) $.
verina73-program-syntax
  $a class ( VERINA73SmallestMissing A ) $.
verina73-postcondition-syntax
  $a wff ( VERINA73Post A B ) $.

verina73-sorted-list-definition $a |- (
  VERINA73SortedList A
) = A $.

${
  $d k p s A B C $.

  verina73-search-graph-definition $a |- (
    VERINA73SearchGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. NN0
    )
    /\
    E. p e. NN0 E. s e. Word NN0
      (
        p <_ ( # ` A )
        /\
        (
          (
            ( # ` s ) = ( p + 1 )
            /\
            ( s ` 0 ) = B
          )
          /\
          (
            A. k e. ( 0 ..^ p )
              (
                ( A ` k ) <_ ( s ` k )
                /\
                (
                  s ` ( k + 1 )
                ) = if (
                  ( A ` k ) = ( s ` k ) ,
                  ( ( s ` k ) + 1 ) ,
                  ( s ` k )
                )
              )
            /\
            (
              (
                p = ( # ` A )
                \/
                ( s ` p ) < ( A ` p )
              )
              /\
              C = ( s ` p )
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina73-search-definition $a |- (
    VERINA73Search A B
  ) = (
    iota_ y e. NN0
      ( VERINA73SearchGraph A B y )
  ) $.
$}

${
  $d i j A $.

  verina73-precondition-definition $a |- (
    VERINA73Pre A
  ) <-> (
    A e. Word NN0
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) < ( A ` j )
        )
  ) $.
$}

verina73-program-definition $a |- (
  VERINA73SmallestMissing A
) = (
  VERINA73Search
    ( VERINA73SortedList A )
    0
) $.

${
  $d x A B $.

  verina73-postcondition-definition $a |- (
    VERINA73Post A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    (
      -. B e. ran A
      /\
      A. x e. NN0
        (
          x < B
          ->
          x e. ran A
        )
    )
  ) $.
$}

verina-advanced-73-smallest-missing $a |- A. w e. Word NN0
  (
    ( VERINA73Pre w )
    ->
    (
      VERINA73Post
        w
        ( VERINA73SmallestMissing w )
    )
  )
$.
