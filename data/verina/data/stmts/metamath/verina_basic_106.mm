$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_106 (verina__metamath__verina_basic_106), catalog title
  arraySum: the exact bounds-defaulted recursive integer-array program
  computes the elementwise sum of two equal-length arrays and satisfies its
  output-size and pointwise-sum correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set. The empty word (/) is the
  inhabited default value of an integer array.

  VERINAB106GetBang reproduces Lean Array.get! on integer arrays, including
  its default value zero outside the array. VERINAB106SetBangGraph and its
  iota-selected function reproduce Array.set!, including unchanged-array
  behavior at an out-of-range index. VERINAB106ZeroArray is exactly
  Array.mkArray n 0.

  VERINAB106LoopGraph is the exact finite execution trace of the local source
  loop for all array, length, starting-index, and accumulator arguments. Its
  trace has max(n - i, 0) transitions. Transition k reads both inputs at
  i + k with get!, adds those integers, and applies set! to the current
  accumulator. VERINAB106Loop selects the unique final accumulator.
  VERINAB106ArraySum preserves the source size-mismatch panic branch as the
  empty-array inhabited default; on equal sizes it initializes a zero array
  of a.size entries and invokes the loop at index zero with n = a.size.

  VERINAB106Pre preserves the equal-size precondition. VERINAB106Post
  preserves the result-size equality and the universal indexed sum equation.
  The proof-valued precondition argument has no computational effect and the
  postcondition does not inspect it, so the final correctness assertion
  represents it by its explicit precondition antecedent. Every earlier $a is
  syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB106NatSub VERINAB106GetBang
  VERINAB106SetBangGraph VERINAB106SetBang
  VERINAB106ZeroArrayGraph VERINAB106ZeroArray
  VERINAB106LoopGraph VERINAB106Loop
  VERINAB106Pre VERINAB106ArraySum VERINAB106Post
$.

verinab106-nat-sub-syntax
  $a class ( VERINAB106NatSub A B ) $.
verinab106-get-bang-syntax
  $a class ( VERINAB106GetBang A B ) $.
verinab106-set-bang-graph-syntax
  $a wff ( VERINAB106SetBangGraph A B C D ) $.
verinab106-set-bang-syntax
  $a class ( VERINAB106SetBang A B C ) $.
verinab106-zero-array-graph-syntax
  $a wff ( VERINAB106ZeroArrayGraph A B ) $.
verinab106-zero-array-syntax
  $a class ( VERINAB106ZeroArray A ) $.
verinab106-loop-graph-syntax
  $a wff ( VERINAB106LoopGraph A B C D E F ) $.
verinab106-loop-syntax
  $a class ( VERINAB106Loop A B C D E ) $.
verinab106-precondition-syntax
  $a wff ( VERINAB106Pre A B ) $.
verinab106-array-sum-syntax
  $a class ( VERINAB106ArraySum A B ) $.
verinab106-postcondition-syntax
  $a wff ( VERINAB106Post A B C ) $.

verinab106-nat-sub-definition $a |- (
  VERINAB106NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab106-get-bang-definition $a |- (
  VERINAB106GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab106-set-bang-graph-definition $a |- (
    VERINAB106SetBangGraph A B C D
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

  verinab106-set-bang-definition $a |- (
    VERINAB106SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB106SetBangGraph A B C y )
  ) $.
$}

${
  $d k A B $.

  verinab106-zero-array-graph-definition $a |- (
    VERINAB106ZeroArrayGraph A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = A
      /\
      A. k e. ( 0 ..^ A )
        ( B ` k ) = 0
    )
  ) $.
$}

${
  $d y A $.

  verinab106-zero-array-definition $a |- (
    VERINAB106ZeroArray A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB106ZeroArrayGraph A y )
  ) $.
$}

${
  $d k t A B C D E F $.

  verinab106-loop-graph-definition $a |- (
    VERINAB106LoopGraph A B C D E F
  ) <-> (
    (
      (
        (
          (
            A e. Word ZZ
            /\
            B e. Word ZZ
          )
          /\
          (
            C e. NN0
            /\
            D e. NN0
          )
        )
        /\
        E e. Word ZZ
      )
      /\
      F e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = (
            ( VERINAB106NatSub C D ) + 1
          )
          /\
          ( t ` 0 ) = E
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB106NatSub C D )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB106SetBang
                ( t ` k )
                ( D + k )
                (
                  ( VERINAB106GetBang A ( D + k ) )
                  +
                  ( VERINAB106GetBang B ( D + k ) )
                )
            )
          /\
          F = (
            t ` ( VERINAB106NatSub C D )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verinab106-loop-definition $a |- (
    VERINAB106Loop A B C D E
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB106LoopGraph A B C D E y )
  ) $.
$}

verinab106-precondition-definition $a |- (
  VERINAB106Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  ( # ` A ) = ( # ` B )
) $.

verinab106-array-sum-definition $a |- (
  VERINAB106ArraySum A B
) = if (
  ( # ` A ) =/= ( # ` B ) ,
  (/) ,
  (
    VERINAB106Loop
      A
      B
      ( # ` A )
      0
      ( VERINAB106ZeroArray ( # ` A ) )
  )
) $.

${
  $d k A B C $.

  verinab106-postcondition-definition $a |- (
    VERINAB106Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = ( # ` A )
      /\
      A. k e. NN0
        (
          k < ( # ` A )
          ->
          (
            ( VERINAB106GetBang A k )
            +
            ( VERINAB106GetBang B k )
          ) = (
            VERINAB106GetBang C k
          )
        )
    )
  ) $.
$}

verina-basic-106-array-sum $a |- A. a e. Word ZZ
  A. b e. Word ZZ
    (
      ( VERINAB106Pre a b )
      ->
      (
        VERINAB106Post
          a
          b
          ( VERINAB106ArraySum a b )
      )
    )
$.
