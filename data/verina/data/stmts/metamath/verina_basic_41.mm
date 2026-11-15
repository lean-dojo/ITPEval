$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_41
  (verina__metamath__verina_basic_41), catalog title
  hasOnlyOneDistinctElement: the exact executable Boolean indexed scan returns
  true on its empty-array branch and otherwise tests every integer entry
  against the first, under the nonempty precondition, and satisfies its
  complete correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays and their
  toList conversions. For a word w, # ` w is its natural-number length,
  w ` i is zero-based lookup, and 0 ..^ ( # ` w ) is its complete valid-index
  set. The Boolean domain is represented by { 0 , 1 }, with false = 0 and
  true = 1.

  VERINAB41GetBang reproduces Lean Array.get! and List.get! on integer
  sequences, including their inhabited default value zero outside the valid
  indices. VERINAB41NatSub is Lean's truncated natural subtraction.

  VERINAB41LoopGraph is the exact graph of the source local recursive loop
  from an arbitrary natural index. Its stopping offset p is at most the
  number of remaining indices, every earlier inspected entry equals a[0]!,
  and either p exhausts the remaining indices and the loop returns true, or
  p is the first differing entry and the loop returns false. VERINAB41Loop
  selects the unique Boolean fixed by this graph.
  VERINAB41HasOnlyOneDistinctElement preserves the source empty-array branch
  and otherwise invokes the loop at index one after binding the first element
  to a[0]!. Thus the executable result is fixed independently of the
  postcondition and the graph admits no extra outputs.

  VERINAB41ToList is the source Array.toList conversion, extensionally
  identity on finite words. VERINAB41PairwiseEqual is exactly List.Pairwise
  equality over every earlier/later valid-index pair. VERINAB41AnyDifferent
  is exactly List.any (fun x => x != l[0]!), including the get! default.

  VERINAB41Pre preserves the source positive-size precondition.
  VERINAB41Post preserves both source Boolean implications: true implies
  pairwise equality, while false implies that some list entry differs from
  the zeroth get! value. The proof-valued precondition arguments to the
  implementation and postcondition have no computational or propositional
  effect beyond the explicit antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB41GetBang VERINAB41NatSub
  VERINAB41LoopGraph VERINAB41Loop
  VERINAB41Pre VERINAB41HasOnlyOneDistinctElement
  VERINAB41ToList VERINAB41PairwiseEqual VERINAB41AnyDifferent
  VERINAB41Post
$.

verinab41-get-bang-syntax
  $a class ( VERINAB41GetBang A B ) $.
verinab41-nat-sub-syntax
  $a class ( VERINAB41NatSub A B ) $.
verinab41-loop-graph-syntax
  $a wff ( VERINAB41LoopGraph A B C ) $.
verinab41-loop-syntax
  $a class ( VERINAB41Loop A B ) $.
verinab41-precondition-syntax
  $a wff ( VERINAB41Pre A ) $.
verinab41-program-syntax
  $a class ( VERINAB41HasOnlyOneDistinctElement A ) $.
verinab41-to-list-syntax
  $a class ( VERINAB41ToList A ) $.
verinab41-pairwise-equal-syntax
  $a wff ( VERINAB41PairwiseEqual A ) $.
verinab41-any-different-syntax
  $a wff ( VERINAB41AnyDifferent A ) $.
verinab41-postcondition-syntax
  $a wff ( VERINAB41Post A B ) $.

verinab41-get-bang-definition $a |- (
  VERINAB41GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab41-nat-sub-definition $a |- (
  VERINAB41NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d j p A B C $.

  verinab41-loop-graph-definition $a |- (
    VERINAB41LoopGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. { 0 , 1 }
    )
    /\
    E. p e. NN0
      (
        p <_ ( VERINAB41NatSub ( # ` A ) B )
        /\
        (
          A. j e. ( 0 ..^ p )
            (
              VERINAB41GetBang A ( B + j )
            ) = (
              VERINAB41GetBang A 0
            )
          /\
          (
            (
              p = ( VERINAB41NatSub ( # ` A ) B )
              /\
              C = 1
            )
            \/
            (
              (
                p < ( VERINAB41NatSub ( # ` A ) B )
                /\
                (
                  VERINAB41GetBang A ( B + p )
                ) =/= (
                  VERINAB41GetBang A 0
                )
              )
              /\
              C = 0
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab41-loop-definition $a |- (
    VERINAB41Loop A B
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINAB41LoopGraph A B y )
  ) $.
$}

verinab41-precondition-definition $a |- (
  VERINAB41Pre A
) <-> (
  A e. Word ZZ
  /\
  0 < ( # ` A )
) $.

verinab41-program-definition $a |- (
  VERINAB41HasOnlyOneDistinctElement A
) = if (
  ( # ` A ) = 0 ,
  1 ,
  ( VERINAB41Loop A 1 )
) $.

verinab41-to-list-definition $a |- (
  VERINAB41ToList A
) = A $.

${
  $d i j A $.

  verinab41-pairwise-equal-definition $a |- (
    VERINAB41PairwiseEqual A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) = ( A ` j )
        )
  ) $.
$}

${
  $d i A $.

  verinab41-any-different-definition $a |- (
    VERINAB41AnyDifferent A
  ) <-> (
    A e. Word ZZ
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      ( A ` i ) =/= ( VERINAB41GetBang A 0 )
  ) $.
$}

verinab41-postcondition-definition $a |- (
  VERINAB41Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. { 0 , 1 }
  )
  /\
  (
    (
      B = 1
      ->
      (
        VERINAB41PairwiseEqual
          ( VERINAB41ToList A )
      )
    )
    /\
    (
      B = 0
      ->
      (
        VERINAB41AnyDifferent
          ( VERINAB41ToList A )
      )
    )
  )
) $.

verina-basic-41-has-only-one-distinct-element $a |-
  A. w e. Word ZZ
    (
      ( VERINAB41Pre w )
      ->
      (
        VERINAB41Post
          w
          ( VERINAB41HasOnlyOneDistinctElement w )
      )
    )
$.
