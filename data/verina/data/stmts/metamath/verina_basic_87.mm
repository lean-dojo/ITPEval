$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_87
  (verina__metamath__verina_basic_87), catalog title SelectionSort: the exact
  minimum-index and guarded-swap folds sort an arbitrary finite integer array
  into a nondecreasing permutation of its input. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays and their
  toList conversions. For a word w, # ` w is its natural-number size,
  w ` k is zero-based lookup, and 0 ..^ ( # ` w ) is its complete valid
  index set.

  VERINAB87NatSub is Lean's truncated natural subtraction.
  VERINAB87GetBang reproduces Array.get! on integer arrays, including its
  inhabited default value zero outside the array. VERINAB87SetBangGraph and
  its iota-selected function reproduce Array.set!, including unchanged-array
  behavior at an out-of-range index.

  VERINAB87FindMinGraph is the complete finite left-fold trace of
  findMinIndexInRange for every integer array and natural start and finish.
  It has max(finish - start, 0) transitions, starts with candidate start, and
  at transition k compares arr[start + k]! with arr[currentCandidate]!,
  replacing the candidate exactly when the former is strictly smaller.
  VERINAB87FindMinIndexInRange selects the unique final candidate.

  VERINAB87Swap preserves the source guard i < a.size, j < a.size, and
  i != j. When it holds, the function saves a[i]!, writes a[j]! at i, and
  then writes the saved value at j; otherwise it returns a unchanged.

  VERINAB87SortGraph is the complete finite execution trace of SelectionSort's
  List.range a.size fold. At transition i it computes the exact minimum index
  in the current array over the source range beginning at i and ending at the
  original input size, then applies the exact guarded swap at i. Thus
  VERINAB87SelectionSort is fixed by the source computation independently of
  the postcondition and the graph admits no extra output.

  VERINAB87ToList is Array.toList, extensionally the identity on this finite
  word representation. VERINAB87PairwiseLE is exactly List.Pairwise (<=), and
  VERINAB87Perm is List.isPerm, represented equivalently by equality of every
  integer's multiplicity. VERINAB87Pre is the source True precondition on
  typed Array Int inputs, and VERINAB87Post is the source conjunction of
  sortedness and permutation. The proof-valued precondition arguments have no
  computational or propositional effect beyond the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB87NatSub VERINAB87GetBang
  VERINAB87SetBangGraph VERINAB87SetBang
  VERINAB87FindMinGraph VERINAB87FindMinIndexInRange
  VERINAB87Swap VERINAB87SortGraph VERINAB87SelectionSort
  VERINAB87Pre VERINAB87ToList VERINAB87PairwiseLE
  VERINAB87Perm VERINAB87Post
$.

verinab87-nat-sub-syntax
  $a class ( VERINAB87NatSub A B ) $.
verinab87-get-bang-syntax
  $a class ( VERINAB87GetBang A B ) $.
verinab87-set-bang-graph-syntax
  $a wff ( VERINAB87SetBangGraph A B C D ) $.
verinab87-set-bang-syntax
  $a class ( VERINAB87SetBang A B C ) $.
verinab87-find-min-graph-syntax
  $a wff ( VERINAB87FindMinGraph A B C D ) $.
verinab87-find-min-syntax
  $a class ( VERINAB87FindMinIndexInRange A B C ) $.
verinab87-swap-syntax
  $a class ( VERINAB87Swap A B C ) $.
verinab87-sort-graph-syntax
  $a wff ( VERINAB87SortGraph A B ) $.
verinab87-selection-sort-syntax
  $a class ( VERINAB87SelectionSort A ) $.
verinab87-precondition-syntax
  $a wff ( VERINAB87Pre A ) $.
verinab87-to-list-syntax
  $a class ( VERINAB87ToList A ) $.
verinab87-pairwise-le-syntax
  $a wff ( VERINAB87PairwiseLE A ) $.
verinab87-permutation-syntax
  $a wff ( VERINAB87Perm A B ) $.
verinab87-postcondition-syntax
  $a wff ( VERINAB87Post A B ) $.

verinab87-nat-sub-definition $a |- (
  VERINAB87NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab87-get-bang-definition $a |- (
  VERINAB87GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab87-set-bang-graph-definition $a |- (
    VERINAB87SetBangGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. NN0
        )
        /\
        C e. ZZ
      )
      /\
      D e. Word ZZ
    )
    /\
    (
      ( # ` D ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        ( D ` k ) = if (
          k = B ,
          C ,
          ( A ` k )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab87-set-bang-definition $a |- (
    VERINAB87SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB87SetBangGraph A B C y )
  ) $.
$}

${
  $d k t A B C D $.

  verinab87-find-min-graph-definition $a |- (
    VERINAB87FindMinGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. NN0
        )
        /\
        C e. NN0
      )
      /\
      D e. NN0
    )
    /\
    E. t e. Word NN0
      (
        (
          ( # ` t ) = (
            ( VERINAB87NatSub C B ) + 1
          )
          /\
          ( t ` 0 ) = B
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB87NatSub C B )
          )
            (
              t ` ( k + 1 )
            ) = if (
              (
                VERINAB87GetBang
                  A
                  ( B + k )
              ) < (
                VERINAB87GetBang
                  A
                  ( t ` k )
              ) ,
              ( B + k ) ,
              ( t ` k )
            )
          /\
          D = (
            t ` ( VERINAB87NatSub C B )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab87-find-min-definition $a |- (
    VERINAB87FindMinIndexInRange A B C
  ) = (
    iota_ y e. NN0
      ( VERINAB87FindMinGraph A B C y )
  ) $.
$}

verinab87-swap-definition $a |- (
  VERINAB87Swap A B C
) = if (
  (
    (
      B < ( # ` A )
      /\
      C < ( # ` A )
    )
    /\
    -. B = C
  ) ,
  (
    VERINAB87SetBang
      (
        VERINAB87SetBang
          A
          B
          ( VERINAB87GetBang A C )
      )
      C
      ( VERINAB87GetBang A B )
  ) ,
  A
) $.

${
  $d k t A B $.

  verinab87-sort-graph-definition $a |- (
    VERINAB87SortGraph A B
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
          ( t ` 0 ) = A
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB87Swap
                ( t ` k )
                k
                (
                  VERINAB87FindMinIndexInRange
                    ( t ` k )
                    k
                    ( # ` A )
                )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verinab87-selection-sort-definition $a |- (
    VERINAB87SelectionSort A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB87SortGraph A y )
  ) $.
$}

verinab87-precondition-definition $a |- (
  VERINAB87Pre A
) <-> (
  A e. Word ZZ
) $.

verinab87-to-list-definition $a |- (
  VERINAB87ToList A
) = A $.

${
  $d i j A $.

  verinab87-pairwise-le-definition $a |- (
    VERINAB87PairwiseLE A
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
  $d i j x A B $.

  verinab87-permutation-definition $a |- (
    VERINAB87Perm A B
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

verinab87-postcondition-definition $a |- (
  VERINAB87Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    (
      VERINAB87PairwiseLE
        ( VERINAB87ToList B )
    )
    /\
    (
      VERINAB87Perm
        ( VERINAB87ToList A )
        ( VERINAB87ToList B )
    )
  )
) $.

verina-basic-87-selection-sort $a |- A. a e. Word ZZ
  (
    ( VERINAB87Pre a )
    ->
    (
      VERINAB87Post
        a
        ( VERINAB87SelectionSort a )
    )
  )
$.
