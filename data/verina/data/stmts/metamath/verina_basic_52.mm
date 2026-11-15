$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_52
  (verina__metamath__verina_basic_52), catalog title BubbleSort: the exact
  adjacent-swap inner loop and decreasing-bound outer loop sort an arbitrary
  finite integer array into a nondecreasing permutation of its input. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays and their
  toList conversions. For a word w, # ` w is its natural-number length,
  w ` k is zero-based lookup, and 0 ..^ ( # ` w ) is its complete valid
  index set.

  VERINAB52NatSub is Lean's truncated natural subtraction.
  VERINAB52GetBang reproduces Array.get! on integer arrays, including its
  inhabited default value zero outside the array. VERINAB52SetBangGraph and
  its iota-selected function reproduce Array.set!, including unchanged-array
  behavior at an out-of-range index. VERINAB52Swap performs the source's two
  left-to-right set! calls after saving the original entry at its first index.

  VERINAB52InnerGraph is the complete finite execution trace of bubbleInner
  for every natural j and i and every integer array. It has max(i - j, 0)
  transitions. Transition k compares exactly the current entries at j + k
  and j + k + 1 and swaps them precisely when the left entry is greater.
  VERINAB52BubbleInner selects the unique final array fixed by that trace.

  VERINAB52OuterGraph is the complete finite execution trace of bubbleOuter.
  Starting with bound i, its k-th transition invokes bubbleInner at zero with
  bound i - k, so the successive positive bounds are i, i - 1, ..., 1.
  VERINAB52BubbleOuter selects the unique final array. VERINAB52BubbleSort
  preserves the source empty-array branch and otherwise starts bubbleOuter
  at a.size - 1. Thus the executable output is fixed independently of the
  postcondition and neither graph admits additional outputs.

  VERINAB52ToList is Array.toList, extensionally the identity on this finite
  word representation. VERINAB52PairwiseLE is exactly List.Pairwise (<=),
  and VERINAB52Perm is List.isPerm, represented equivalently by equality of
  every integer's multiplicity. VERINAB52Pre is the source True precondition
  on typed Array Int inputs, and VERINAB52Post is the source conjunction of
  sortedness and permutation. The proof-valued precondition arguments have no
  computational or propositional effect beyond the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB52NatSub VERINAB52GetBang
  VERINAB52SetBangGraph VERINAB52SetBang VERINAB52Swap
  VERINAB52InnerGraph VERINAB52BubbleInner
  VERINAB52OuterGraph VERINAB52BubbleOuter
  VERINAB52Pre VERINAB52BubbleSort VERINAB52ToList
  VERINAB52PairwiseLE VERINAB52Perm VERINAB52Post
$.

verinab52-nat-sub-syntax
  $a class ( VERINAB52NatSub A B ) $.
verinab52-get-bang-syntax
  $a class ( VERINAB52GetBang A B ) $.
verinab52-set-bang-graph-syntax
  $a wff ( VERINAB52SetBangGraph A B C D ) $.
verinab52-set-bang-syntax
  $a class ( VERINAB52SetBang A B C ) $.
verinab52-swap-syntax
  $a class ( VERINAB52Swap A B C ) $.
verinab52-inner-graph-syntax
  $a wff ( VERINAB52InnerGraph A B C D ) $.
verinab52-inner-syntax
  $a class ( VERINAB52BubbleInner A B C ) $.
verinab52-outer-graph-syntax
  $a wff ( VERINAB52OuterGraph A B C ) $.
verinab52-outer-syntax
  $a class ( VERINAB52BubbleOuter A B ) $.
verinab52-precondition-syntax
  $a wff ( VERINAB52Pre A ) $.
verinab52-program-syntax
  $a class ( VERINAB52BubbleSort A ) $.
verinab52-to-list-syntax
  $a class ( VERINAB52ToList A ) $.
verinab52-pairwise-le-syntax
  $a wff ( VERINAB52PairwiseLE A ) $.
verinab52-permutation-syntax
  $a wff ( VERINAB52Perm A B ) $.
verinab52-postcondition-syntax
  $a wff ( VERINAB52Post A B ) $.

verinab52-nat-sub-definition $a |- (
  VERINAB52NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab52-get-bang-definition $a |- (
  VERINAB52GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab52-set-bang-graph-definition $a |- (
    VERINAB52SetBangGraph A B C D
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

  verinab52-set-bang-definition $a |- (
    VERINAB52SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB52SetBangGraph A B C y )
  ) $.
$}

verinab52-swap-definition $a |- (
  VERINAB52Swap A B C
) = (
  VERINAB52SetBang
    (
      VERINAB52SetBang
        A
        B
        ( VERINAB52GetBang A C )
    )
    C
    ( VERINAB52GetBang A B )
) $.

${
  $d k t A B C D $.

  verinab52-inner-graph-definition $a |- (
    VERINAB52InnerGraph A B C D
  ) <-> (
    (
      (
        (
          A e. NN0
          /\
          B e. NN0
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
          ( # ` t ) = (
            ( VERINAB52NatSub B A ) + 1
          )
          /\
          ( t ` 0 ) = C
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB52NatSub B A )
          )
            (
              t ` ( k + 1 )
            ) = if (
              (
                VERINAB52GetBang
                  ( t ` k )
                  ( ( A + k ) + 1 )
              ) < (
                VERINAB52GetBang
                  ( t ` k )
                  ( A + k )
              ) ,
              (
                VERINAB52Swap
                  ( t ` k )
                  ( A + k )
                  ( ( A + k ) + 1 )
              ) ,
              ( t ` k )
            )
          /\
          D = (
            t ` ( VERINAB52NatSub B A )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab52-inner-definition $a |- (
    VERINAB52BubbleInner A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB52InnerGraph A B C y )
  ) $.
$}

${
  $d k t A B C $.

  verinab52-outer-graph-definition $a |- (
    VERINAB52OuterGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. Word ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = ( A + 1 )
          /\
          ( t ` 0 ) = B
        )
        /\
        (
          A. k e. ( 0 ..^ A )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB52BubbleInner
                0
                ( VERINAB52NatSub A k )
                ( t ` k )
            )
          /\
          C = ( t ` A )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab52-outer-definition $a |- (
    VERINAB52BubbleOuter A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB52OuterGraph A B y )
  ) $.
$}

verinab52-precondition-definition $a |- (
  VERINAB52Pre A
) <-> (
  A e. Word ZZ
) $.

verinab52-program-definition $a |- (
  VERINAB52BubbleSort A
) = if (
  ( # ` A ) = 0 ,
  A ,
  (
    VERINAB52BubbleOuter
      ( VERINAB52NatSub ( # ` A ) 1 )
      A
  )
) $.

verinab52-to-list-definition $a |- (
  VERINAB52ToList A
) = A $.

${
  $d i j A $.

  verinab52-pairwise-le-definition $a |- (
    VERINAB52PairwiseLE A
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

  verinab52-permutation-definition $a |- (
    VERINAB52Perm A B
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

verinab52-postcondition-definition $a |- (
  VERINAB52Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    (
      VERINAB52PairwiseLE
        ( VERINAB52ToList B )
    )
    /\
    (
      VERINAB52Perm
        ( VERINAB52ToList B )
        ( VERINAB52ToList A )
    )
  )
) $.

verina-basic-52-bubble-sort $a |- A. w e. Word ZZ
  (
    ( VERINAB52Pre w )
    ->
    (
      VERINAB52Post
        w
        ( VERINAB52BubbleSort w )
    )
  )
$.
