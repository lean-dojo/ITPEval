$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_105 (verina__metamath__verina_basic_105), catalog title
  arrayProduct: the exact bounds-defaulted recursive integer-array program
  computes the elementwise product of two equal-length arrays and satisfies
  its output-size and pointwise-product correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINAB105GetBang reproduces Lean Array.get! on integer arrays, including
  its default value zero outside the array. VERINAB105SetBangGraph and its
  iota-selected function reproduce Array.set!, including unchanged-array
  behavior at an out-of-range index. VERINAB105ZeroArray is exactly
  Array.mkArray len 0.

  VERINAB105LoopGraph is the exact finite execution trace of the source loop
  for all array, length, starting-index, and accumulator arguments. Its trace
  has max(len - i, 0) transitions. Transition k reads both inputs at i + k
  with get!, multiplies those integers, and applies set! to the current
  accumulator. VERINAB105Loop selects the unique final accumulator.
  VERINAB105ArrayProduct initializes a zero array of a.size entries and invokes
  that loop at index zero with len = a.size, exactly as in the Lean program.

  VERINAB105Pre preserves the equal-size precondition. VERINAB105Post
  preserves the result-size equality and the universal indexed product
  equation. The proof-valued precondition arguments have no computational
  effect and the postcondition does not inspect them, so the final correctness
  assertion represents them by its explicit precondition antecedent. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB105NatSub VERINAB105GetBang
  VERINAB105SetBangGraph VERINAB105SetBang
  VERINAB105ZeroArrayGraph VERINAB105ZeroArray
  VERINAB105LoopGraph VERINAB105Loop
  VERINAB105Pre VERINAB105ArrayProduct VERINAB105Post
$.

verinab105-nat-sub-syntax
  $a class ( VERINAB105NatSub A B ) $.
verinab105-get-bang-syntax
  $a class ( VERINAB105GetBang A B ) $.
verinab105-set-bang-graph-syntax
  $a wff ( VERINAB105SetBangGraph A B C D ) $.
verinab105-set-bang-syntax
  $a class ( VERINAB105SetBang A B C ) $.
verinab105-zero-array-graph-syntax
  $a wff ( VERINAB105ZeroArrayGraph A B ) $.
verinab105-zero-array-syntax
  $a class ( VERINAB105ZeroArray A ) $.
verinab105-loop-graph-syntax
  $a wff ( VERINAB105LoopGraph A B C D E F ) $.
verinab105-loop-syntax
  $a class ( VERINAB105Loop A B C D E ) $.
verinab105-precondition-syntax
  $a wff ( VERINAB105Pre A B ) $.
verinab105-array-product-syntax
  $a class ( VERINAB105ArrayProduct A B ) $.
verinab105-postcondition-syntax
  $a wff ( VERINAB105Post A B C ) $.

verinab105-nat-sub-definition $a |- (
  VERINAB105NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab105-get-bang-definition $a |- (
  VERINAB105GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab105-set-bang-graph-definition $a |- (
    VERINAB105SetBangGraph A B C D
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

  verinab105-set-bang-definition $a |- (
    VERINAB105SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB105SetBangGraph A B C y )
  ) $.
$}

${
  $d k A B $.

  verinab105-zero-array-graph-definition $a |- (
    VERINAB105ZeroArrayGraph A B
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

  verinab105-zero-array-definition $a |- (
    VERINAB105ZeroArray A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB105ZeroArrayGraph A y )
  ) $.
$}

${
  $d k t A B C D E F $.

  verinab105-loop-graph-definition $a |- (
    VERINAB105LoopGraph A B C D E F
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
            ( VERINAB105NatSub C D ) + 1
          )
          /\
          ( t ` 0 ) = E
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB105NatSub C D )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB105SetBang
                ( t ` k )
                ( D + k )
                (
                  ( VERINAB105GetBang A ( D + k ) )
                  x.
                  ( VERINAB105GetBang B ( D + k ) )
                )
            )
          /\
          F = (
            t ` ( VERINAB105NatSub C D )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verinab105-loop-definition $a |- (
    VERINAB105Loop A B C D E
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB105LoopGraph A B C D E y )
  ) $.
$}

verinab105-precondition-definition $a |- (
  VERINAB105Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  ( # ` A ) = ( # ` B )
) $.

verinab105-array-product-definition $a |- (
  VERINAB105ArrayProduct A B
) = (
  VERINAB105Loop
    A
    B
    ( # ` A )
    0
    ( VERINAB105ZeroArray ( # ` A ) )
) $.

${
  $d k A B C $.

  verinab105-postcondition-definition $a |- (
    VERINAB105Post A B C
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
            ( VERINAB105GetBang A k )
            x.
            ( VERINAB105GetBang B k )
          ) = (
            VERINAB105GetBang C k
          )
        )
    )
  ) $.
$}

verina-basic-105-array-product $a |- A. a e. Word ZZ
  A. b e. Word ZZ
    (
      ( VERINAB105Pre a b )
      ->
      (
        VERINAB105Post
          a
          b
          ( VERINAB105ArrayProduct a b )
      )
    )
$.
