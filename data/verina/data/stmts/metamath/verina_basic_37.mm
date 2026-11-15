$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_37
  (verina__metamath__verina_basic_37), catalog title findFirstOccurrence:
  the exact executable early-exit scan of a nondecreasing finite integer
  array returns the first target index, or integer -1 when the target is
  absent, and satisfies its complete correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ n is the natural index set below n.

  VERINAB37GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB37NatSub is
  Lean's truncated natural subtraction, and VERINAB37ToNat is Lean Int.toNat.

  VERINAB37LoopGraph is the exact computation of the source local loop for
  every typed array, target, and natural starting index. Its offset p skips
  exactly the consecutive entries strictly below the target. It stops at the
  first remaining entry greater than or equal to the target, or at the end
  of the array. At a stopping entry it returns the corresponding index
  exactly when that entry equals the target and otherwise returns -1; reaching
  the end also returns -1. VERINAB37Loop selects the unique integer fixed by
  this graph, and VERINAB37FindFirstOccurrence invokes it at index zero.
  Thus the executable result is fixed independently of the postcondition and
  the graph admits no extra outputs, including on unsorted typed arrays.

  VERINAB37PairwiseLE is exactly List.Pairwise with integer <=, expressed over
  every earlier/later index pair. VERINAB37Pre preserves that sortedness
  precondition. VERINAB37Post preserves all three source conjuncts: the
  result is -1 or nonnegative; a nonnegative result is an in-bounds target
  index with no earlier target occurrence; and -1 means no valid array index
  contains the target. The proof-valued precondition arguments are
  computationally and propositionally unused beyond the explicit antecedent
  in the final correctness assertion. Every earlier $a is syntax or a
  faithful definition required by this rendering, and this database has no
  $p declaration.
$)

$c
  VERINAB37GetBang VERINAB37NatSub VERINAB37ToNat
  VERINAB37PairwiseLE VERINAB37Pre
  VERINAB37LoopGraph VERINAB37Loop
  VERINAB37FindFirstOccurrence VERINAB37Post
$.

verinab37-get-bang-syntax
  $a class ( VERINAB37GetBang A B ) $.
verinab37-nat-sub-syntax
  $a class ( VERINAB37NatSub A B ) $.
verinab37-to-nat-syntax
  $a class ( VERINAB37ToNat A ) $.
verinab37-pairwise-le-syntax
  $a wff ( VERINAB37PairwiseLE A ) $.
verinab37-precondition-syntax
  $a wff ( VERINAB37Pre A B ) $.
verinab37-loop-graph-syntax
  $a wff ( VERINAB37LoopGraph A B C D ) $.
verinab37-loop-syntax
  $a class ( VERINAB37Loop A B C ) $.
verinab37-program-syntax
  $a class ( VERINAB37FindFirstOccurrence A B ) $.
verinab37-postcondition-syntax
  $a wff ( VERINAB37Post A B C ) $.

verinab37-get-bang-definition $a |- (
  VERINAB37GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab37-nat-sub-definition $a |- (
  VERINAB37NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab37-to-nat-definition $a |- (
  VERINAB37ToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

${
  $d i j A $.

  verinab37-pairwise-le-definition $a |- (
    VERINAB37PairwiseLE A
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

verinab37-precondition-definition $a |- (
  VERINAB37Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  ( VERINAB37PairwiseLE A )
) $.

${
  $d j p A B C D $.

  verinab37-loop-graph-definition $a |- (
    VERINAB37LoopGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. ZZ
        )
        /\
        C e. NN0
      )
      /\
      D e. ZZ
    )
    /\
    E. p e. NN0
      (
        p <_ ( VERINAB37NatSub ( # ` A ) C )
        /\
        (
          A. j e. ( 0 ..^ p )
            ( A ` ( C + j ) ) < B
          /\
          (
            p < ( VERINAB37NatSub ( # ` A ) C )
            ->
            B <_ ( A ` ( C + p ) )
          )
          /\
          D = if (
            (
              ( C + p ) < ( # ` A )
              /\
              ( A ` ( C + p ) ) = B
            ) ,
            ( C + p ) ,
            ( -u 1 )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab37-loop-definition $a |- (
    VERINAB37Loop A B C
  ) = (
    iota_ y e. ZZ
      ( VERINAB37LoopGraph A B C y )
  ) $.
$}

verinab37-program-definition $a |- (
  VERINAB37FindFirstOccurrence A B
) = (
  VERINAB37Loop A B 0
) $.

${
  $d i A B C $.

  verinab37-postcondition-definition $a |- (
    VERINAB37Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. ZZ
    )
    /\
    (
      (
        C = ( -u 1 )
        \/
        0 <_ C
      )
      /\
      (
        (
          0 <_ C
          ->
          (
            ( VERINAB37ToNat C ) < ( # ` A )
            /\
            (
              VERINAB37GetBang A ( VERINAB37ToNat C )
            ) = B
            /\
            A. i e. NN0
              (
                i < ( VERINAB37ToNat C )
                ->
                ( VERINAB37GetBang A i ) =/= B
              )
          )
        )
        /\
        (
          C = ( -u 1 )
          ->
          A. i e. NN0
            (
              i < ( # ` A )
              ->
              ( VERINAB37GetBang A i ) =/= B
            )
        )
      )
    )
  ) $.
$}

verina-basic-37-find-first-occurrence
  $a |- A. w e. Word ZZ
    A. t e. ZZ
      (
        ( VERINAB37Pre w t )
        ->
        (
          VERINAB37Post
            w
            t
            ( VERINAB37FindFirstOccurrence w t )
        )
      )
  $.
