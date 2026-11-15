$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_85
  (verina__metamath__verina_basic_85), catalog title reverse: the exact
  executable recursive integer-array program swaps mirrored entries from the
  outside inward and satisfies the size-and-pointwise reversal contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` i is zero-based lookup, and
  0 ..^ n is the complete set of natural indices below n.

  VERINAB85NatSub is Lean's truncated natural subtraction.
  VERINAB85GetBang reproduces Array.get! on integer arrays, including its
  inhabited default value zero outside the array. VERINAB85SetBangGraph and
  its iota-selected function reproduce Array.set!, including unchanged-array
  behavior at an out-of-range index. VERINAB85Swap saves the original entry
  at the left index and then performs the source's two set! calls in order.
  VERINAB85Half is Lean natural-number division of the array size by two.

  VERINAB85CoreGraph is the exact finite execution trace of reverse_core for
  every integer array and natural starting index. Its trace has
  max(floor(arr.size / 2) - i, 0) transitions. At transition k it swaps the
  current entries at i + k and arr.size - 1 - (i + k), preserving the source
  guard, left-associated truncated subtraction, saved temporary value,
  recursive index increment, get!, and set! behavior. Since every set!
  preserves array size, these are exactly the successive recursive calls.
  VERINAB85Core selects the unique final array fixed by that trace and hence
  admits no output beyond the source computation.

  VERINAB85Pre is the source True precondition on typed Array Int inputs.
  VERINAB85Reverse invokes the exact core computation at index zero.
  VERINAB85Post preserves the source result-size equation and universal
  mirrored get! equation with its original natural-number bound and
  left-associated subtraction. The proof-valued precondition arguments to
  the implementation and postcondition are computationally and
  propositionally unused beyond the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB85NatSub VERINAB85GetBang
  VERINAB85SetBangGraph VERINAB85SetBang VERINAB85Swap
  VERINAB85Half VERINAB85CoreGraph VERINAB85Core
  VERINAB85Pre VERINAB85Reverse VERINAB85Post
$.

verinab85-nat-sub-syntax
  $a class ( VERINAB85NatSub A B ) $.
verinab85-get-bang-syntax
  $a class ( VERINAB85GetBang A B ) $.
verinab85-set-bang-graph-syntax
  $a wff ( VERINAB85SetBangGraph A B C D ) $.
verinab85-set-bang-syntax
  $a class ( VERINAB85SetBang A B C ) $.
verinab85-swap-syntax
  $a class ( VERINAB85Swap A B C ) $.
verinab85-half-syntax
  $a class ( VERINAB85Half A ) $.
verinab85-core-graph-syntax
  $a wff ( VERINAB85CoreGraph A B C ) $.
verinab85-core-syntax
  $a class ( VERINAB85Core A B ) $.
verinab85-precondition-syntax
  $a wff ( VERINAB85Pre A ) $.
verinab85-program-syntax
  $a class ( VERINAB85Reverse A ) $.
verinab85-postcondition-syntax
  $a wff ( VERINAB85Post A B ) $.

verinab85-nat-sub-definition $a |- (
  VERINAB85NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab85-get-bang-definition $a |- (
  VERINAB85GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab85-set-bang-graph-definition $a |- (
    VERINAB85SetBangGraph A B C D
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

  verinab85-set-bang-definition $a |- (
    VERINAB85SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB85SetBangGraph A B C y )
  ) $.
$}

verinab85-swap-definition $a |- (
  VERINAB85Swap A B C
) = (
  VERINAB85SetBang
    (
      VERINAB85SetBang
        A
        B
        ( VERINAB85GetBang A C )
    )
    C
    ( VERINAB85GetBang A B )
) $.

verinab85-half-definition $a |- (
  VERINAB85Half A
) = (
  |_ ` ( ( # ` A ) / 2 )
) $.

${
  $d k t A B C $.

  verinab85-core-graph-definition $a |- (
    VERINAB85CoreGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = (
            ( VERINAB85NatSub ( VERINAB85Half A ) B ) + 1
          )
          /\
          ( t ` 0 ) = A
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB85NatSub ( VERINAB85Half A ) B )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB85Swap
                ( t ` k )
                ( B + k )
                (
                  VERINAB85NatSub
                    (
                      VERINAB85NatSub
                        ( # ` ( t ` k ) )
                        1
                    )
                    ( B + k )
                )
            )
          /\
          C = (
            t ` (
              VERINAB85NatSub ( VERINAB85Half A ) B
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab85-core-definition $a |- (
    VERINAB85Core A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB85CoreGraph A B y )
  ) $.
$}

verinab85-precondition-definition $a |- (
  VERINAB85Pre A
) <-> (
  A e. Word ZZ
) $.

verinab85-program-definition $a |- (
  VERINAB85Reverse A
) = (
  VERINAB85Core A 0
) $.

${
  $d i A B $.

  verinab85-postcondition-definition $a |- (
    VERINAB85Post A B
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
      A. i e. NN0
        (
          i < ( # ` A )
          ->
          (
            VERINAB85GetBang B i
          ) = (
            VERINAB85GetBang
              A
              (
                VERINAB85NatSub
                  ( VERINAB85NatSub ( # ` A ) 1 )
                  i
              )
          )
        )
    )
  ) $.
$}

verina-basic-85-reverse $a |- A. a e. Word ZZ
  (
    ( VERINAB85Pre a )
    ->
    (
      VERINAB85Post
        a
        ( VERINAB85Reverse a )
    )
  )
$.
