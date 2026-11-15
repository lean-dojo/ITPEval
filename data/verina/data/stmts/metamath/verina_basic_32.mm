$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_32
  (verina__metamath__verina_basic_32), catalog title swapFirstAndLast: the
  exact executable integer-array program swaps the first and last entries of
  a nonempty array, preserves every intervening entry, and satisfies its
  complete size-and-index correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ n is the index set corresponding to List.range n.

  VERINAB32NatSub is Lean's truncated natural subtraction.
  VERINAB32GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array.
  VERINAB32SetBangGraph and its iota-selected function reproduce Array.set!,
  including unchanged-array behavior at an out-of-range index.

  VERINAB32SwapFirstAndLast first reads both endpoint values from the original
  array, writes the original last value at index zero, and then writes the
  original first value at the truncated index a.size - 1. This is exactly the
  source let-binding and left-to-right set! composition, so the executable
  output is fixed independently of the postcondition and admits no additional
  results.

  VERINAB32Pre is exactly the nonempty-array precondition. VERINAB32Post
  preserves the source size equation, both bounds-defaulted endpoint
  equations, and List.range (result.size - 2).all as a universal equality
  over the same truncated natural range after adding one to each index. The
  proof-valued precondition arguments have no computational or propositional
  effect beyond the explicit antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB32NatSub VERINAB32GetBang
  VERINAB32SetBangGraph VERINAB32SetBang
  VERINAB32Pre VERINAB32SwapFirstAndLast VERINAB32Post
$.

verinab32-nat-sub-syntax
  $a class ( VERINAB32NatSub A B ) $.
verinab32-get-bang-syntax
  $a class ( VERINAB32GetBang A B ) $.
verinab32-set-bang-graph-syntax
  $a wff ( VERINAB32SetBangGraph A B C D ) $.
verinab32-set-bang-syntax
  $a class ( VERINAB32SetBang A B C ) $.
verinab32-precondition-syntax
  $a wff ( VERINAB32Pre A ) $.
verinab32-program-syntax
  $a class ( VERINAB32SwapFirstAndLast A ) $.
verinab32-postcondition-syntax
  $a wff ( VERINAB32Post A B ) $.

verinab32-nat-sub-definition $a |- (
  VERINAB32NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab32-get-bang-definition $a |- (
  VERINAB32GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i A B C D $.

  verinab32-set-bang-graph-definition $a |- (
    VERINAB32SetBangGraph A B C D
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
      A. i e. ( 0 ..^ ( # ` A ) )
        ( D ` i ) = if (
          i = B ,
          C ,
          ( A ` i )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab32-set-bang-definition $a |- (
    VERINAB32SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB32SetBangGraph A B C y )
  ) $.
$}

verinab32-precondition-definition $a |- (
  VERINAB32Pre A
) <-> (
  A e. Word ZZ
  /\
  0 < ( # ` A )
) $.

verinab32-program-definition $a |- (
  VERINAB32SwapFirstAndLast A
) = (
  VERINAB32SetBang
    (
      VERINAB32SetBang
        A
        0
        (
          VERINAB32GetBang
            A
            ( VERINAB32NatSub ( # ` A ) 1 )
        )
    )
    ( VERINAB32NatSub ( # ` A ) 1 )
    ( VERINAB32GetBang A 0 )
) $.

${
  $d i A B $.

  verinab32-postcondition-definition $a |- (
    VERINAB32Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      (
        ( VERINAB32GetBang B 0 )
        =
        (
          VERINAB32GetBang
            A
            ( VERINAB32NatSub ( # ` A ) 1 )
        )
      )
      /\
      (
        (
          VERINAB32GetBang
            B
            ( VERINAB32NatSub ( # ` B ) 1 )
        )
        =
        ( VERINAB32GetBang A 0 )
      )
      /\
      A. i e. (
        0 ..^ ( VERINAB32NatSub ( # ` B ) 2 )
      )
        (
          VERINAB32GetBang B ( i + 1 )
        ) = (
          VERINAB32GetBang A ( i + 1 )
        )
    )
  ) $.
$}

verina-basic-32-swap-first-and-last $a |- A. a e. Word ZZ
  (
    ( VERINAB32Pre a )
    ->
    (
      VERINAB32Post
        a
        ( VERINAB32SwapFirstAndLast a )
    )
  )
$.
