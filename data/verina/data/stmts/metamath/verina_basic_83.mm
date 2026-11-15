$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_83
  (verina__metamath__verina_basic_83), catalog title concat: the exact
  recursive integer-array program concatenates two arbitrary finite arrays
  and satisfies the output-size and two-part pointwise correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB83NatSub is truncated natural subtraction. VERINAB83GetBang
  reproduces Lean Array.get! on integer arrays, including its inhabited
  default value zero outside the array. VERINAB83SetBangGraph and its
  iota-selected function reproduce Array.set!, including unchanged-array
  behavior at an out-of-range index. VERINAB83ZeroArray is exactly
  Array.mkArray n 0.

  VERINAB83LoopGraph is the exact finite execution trace of the source local
  loop for arbitrary inputs, bound n, starting index i, and accumulator. Its
  trace has max(n - i, 0) transitions. Transition k writes index i + k with
  a[i + k]! when that index is below a.size, and otherwise writes
  b[(i + k) - a.size]!. VERINAB83Loop selects the unique final accumulator.
  VERINAB83Concat sets n to a.size + b.size, initializes the corresponding
  zero array, and invokes that exact loop at index zero.

  VERINAB83Pre preserves the source True precondition on typed Array Int
  inputs. VERINAB83Post preserves the result-size equation and both universal
  pointwise equations, including their original natural-number bounds. The
  proof-valued precondition argument has no computational effect and the
  postcondition does not inspect it, so the final correctness assertion
  represents it by its explicit precondition antecedent. Every earlier $a is
  syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB83NatSub VERINAB83GetBang
  VERINAB83SetBangGraph VERINAB83SetBang
  VERINAB83ZeroArrayGraph VERINAB83ZeroArray
  VERINAB83LoopGraph VERINAB83Loop
  VERINAB83Pre VERINAB83Concat VERINAB83Post
$.

verinab83-nat-sub-syntax
  $a class ( VERINAB83NatSub A B ) $.
verinab83-get-bang-syntax
  $a class ( VERINAB83GetBang A B ) $.
verinab83-set-bang-graph-syntax
  $a wff ( VERINAB83SetBangGraph A B C D ) $.
verinab83-set-bang-syntax
  $a class ( VERINAB83SetBang A B C ) $.
verinab83-zero-array-graph-syntax
  $a wff ( VERINAB83ZeroArrayGraph A B ) $.
verinab83-zero-array-syntax
  $a class ( VERINAB83ZeroArray A ) $.
verinab83-loop-graph-syntax
  $a wff ( VERINAB83LoopGraph A B C D E F ) $.
verinab83-loop-syntax
  $a class ( VERINAB83Loop A B C D E ) $.
verinab83-precondition-syntax
  $a wff ( VERINAB83Pre A B ) $.
verinab83-concat-syntax
  $a class ( VERINAB83Concat A B ) $.
verinab83-postcondition-syntax
  $a wff ( VERINAB83Post A B C ) $.

verinab83-nat-sub-definition $a |- (
  VERINAB83NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab83-get-bang-definition $a |- (
  VERINAB83GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab83-set-bang-graph-definition $a |- (
    VERINAB83SetBangGraph A B C D
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

  verinab83-set-bang-definition $a |- (
    VERINAB83SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB83SetBangGraph A B C y )
  ) $.
$}

${
  $d k A B $.

  verinab83-zero-array-graph-definition $a |- (
    VERINAB83ZeroArrayGraph A B
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

  verinab83-zero-array-definition $a |- (
    VERINAB83ZeroArray A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB83ZeroArrayGraph A y )
  ) $.
$}

${
  $d k t A B C D E F $.

  verinab83-loop-graph-definition $a |- (
    VERINAB83LoopGraph A B C D E F
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
            ( VERINAB83NatSub C D ) + 1
          )
          /\
          ( t ` 0 ) = E
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB83NatSub C D )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB83SetBang
                ( t ` k )
                ( D + k )
                if (
                  ( D + k ) < ( # ` A ) ,
                  ( VERINAB83GetBang A ( D + k ) ) ,
                  (
                    VERINAB83GetBang
                      B
                      (
                        VERINAB83NatSub
                          ( D + k )
                          ( # ` A )
                      )
                  )
                )
            )
          /\
          F = (
            t ` ( VERINAB83NatSub C D )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verinab83-loop-definition $a |- (
    VERINAB83Loop A B C D E
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB83LoopGraph A B C D E y )
  ) $.
$}

verinab83-precondition-definition $a |- (
  VERINAB83Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. Word ZZ
) $.

verinab83-concat-definition $a |- (
  VERINAB83Concat A B
) = (
  VERINAB83Loop
    A
    B
    (
      ( # ` A ) + ( # ` B )
    )
    0
    (
      VERINAB83ZeroArray
        (
          ( # ` A ) + ( # ` B )
        )
    )
) $.

${
  $d k A B C $.

  verinab83-postcondition-definition $a |- (
    VERINAB83Post A B C
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
      ( # ` C ) = (
        ( # ` A ) + ( # ` B )
      )
      /\
      (
        A. k e. NN0
          (
            k < ( # ` A )
            ->
            (
              VERINAB83GetBang C k
            ) = (
              VERINAB83GetBang A k
            )
          )
        /\
        A. k e. NN0
          (
            k < ( # ` B )
            ->
            (
              VERINAB83GetBang
                C
                ( k + ( # ` A ) )
            ) = (
              VERINAB83GetBang B k
            )
          )
      )
    )
  ) $.
$}

verina-basic-83-concat $a |- A. a e. Word ZZ
  A. b e. Word ZZ
    (
      ( VERINAB83Pre a b )
      ->
      (
        VERINAB83Post
          a
          b
          ( VERINAB83Concat a b )
      )
    )
$.
