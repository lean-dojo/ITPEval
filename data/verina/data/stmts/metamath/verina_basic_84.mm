$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_84
  (verina__metamath__verina_basic_84), catalog title replace: the exact
  executable recursive integer-array program replaces every entry greater
  than an arbitrary integer threshold with negative one, leaves every other
  entry unchanged, and satisfies its size-and-pointwise correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` i is zero-based lookup, and
  0 ..^ n is the set of natural indices below n.

  VERINAB84NatSub is Lean's truncated natural subtraction.
  VERINAB84GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB84SetBangGraph
  and its iota-selected function reproduce Array.set!, including unchanged
  array behavior at an out-of-range index.

  VERINAB84LoopGraph is the exact finite execution trace of replace_loop for
  every immutable old array, integer threshold, natural starting index, and
  accumulator array. Its trace has max(oldArr.size - i, 0) transitions.
  Transition j reads oldArr[i+j]! and replaces accumulator index i+j with
  negative one exactly when that value is greater than the threshold;
  otherwise the accumulator is unchanged. Thus the trace preserves the
  source guard, branch order, recursive index increment, get!, and set!
  behavior. VERINAB84Loop selects the unique final accumulator.

  VERINAB84Pre is the source True precondition on typed Array Int and Int
  inputs. VERINAB84Replace invokes the exact loop with starting index zero
  and the input array as both immutable old array and initial accumulator.
  VERINAB84Post preserves the result-size equation and both universal
  pointwise implications at every valid input index. The proof-valued
  precondition arguments to the implementation and postcondition are
  computationally and propositionally unused beyond the explicit
  precondition antecedent in the final correctness assertion. Every earlier
  $a is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB84NatSub VERINAB84GetBang
  VERINAB84SetBangGraph VERINAB84SetBang
  VERINAB84LoopGraph VERINAB84Loop
  VERINAB84Pre VERINAB84Replace VERINAB84Post
$.

verinab84-nat-sub-syntax
  $a class ( VERINAB84NatSub A B ) $.
verinab84-get-bang-syntax
  $a class ( VERINAB84GetBang A B ) $.
verinab84-set-bang-graph-syntax
  $a wff ( VERINAB84SetBangGraph A B C D ) $.
verinab84-set-bang-syntax
  $a class ( VERINAB84SetBang A B C ) $.
verinab84-loop-graph-syntax
  $a wff ( VERINAB84LoopGraph A B C D E ) $.
verinab84-loop-syntax
  $a class ( VERINAB84Loop A B C D ) $.
verinab84-precondition-syntax
  $a wff ( VERINAB84Pre A B ) $.
verinab84-program-syntax
  $a class ( VERINAB84Replace A B ) $.
verinab84-postcondition-syntax
  $a wff ( VERINAB84Post A B C ) $.

verinab84-nat-sub-definition $a |- (
  VERINAB84NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab84-get-bang-definition $a |- (
  VERINAB84GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i A B C D $.

  verinab84-set-bang-graph-definition $a |- (
    VERINAB84SetBangGraph A B C D
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

  verinab84-set-bang-definition $a |- (
    VERINAB84SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB84SetBangGraph A B C y )
  ) $.
$}

${
  $d j t A B C D E $.

  verinab84-loop-graph-definition $a |- (
    VERINAB84LoopGraph A B C D E
  ) <-> (
    (
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
        D e. Word ZZ
      )
      /\
      E e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = (
            ( VERINAB84NatSub ( # ` A ) C ) + 1
          )
          /\
          ( t ` 0 ) = D
        )
        /\
        (
          A. j e. (
            0 ..^ ( VERINAB84NatSub ( # ` A ) C )
          )
            (
              t ` ( j + 1 )
            ) = if (
              B < (
                VERINAB84GetBang A ( C + j )
              ) ,
              (
                VERINAB84SetBang
                  ( t ` j )
                  ( C + j )
                  ( -u 1 )
              ) ,
              ( t ` j )
            )
          /\
          E = (
            t ` ( VERINAB84NatSub ( # ` A ) C )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D $.

  verinab84-loop-definition $a |- (
    VERINAB84Loop A B C D
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB84LoopGraph A B C D y )
  ) $.
$}

verinab84-precondition-definition $a |- (
  VERINAB84Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. ZZ
) $.

verinab84-program-definition $a |- (
  VERINAB84Replace A B
) = (
  VERINAB84Loop A B 0 A
) $.

${
  $d i A B C $.

  verinab84-postcondition-definition $a |- (
    VERINAB84Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = ( # ` A )
      /\
      (
        A. i e. NN0
          (
            i < ( # ` A )
            ->
            (
              B < ( VERINAB84GetBang A i )
              ->
              ( VERINAB84GetBang C i ) = ( -u 1 )
            )
          )
        /\
        A. i e. NN0
          (
            i < ( # ` A )
            ->
            (
              ( VERINAB84GetBang A i ) <_ B
              ->
              (
                VERINAB84GetBang C i
              ) = (
                VERINAB84GetBang A i
              )
            )
          )
      )
    )
  ) $.
$}

verina-basic-84-replace $a |- A. a e. Word ZZ
  A. k e. ZZ
    (
      ( VERINAB84Pre a k )
      ->
      (
        VERINAB84Post
          a
          k
          ( VERINAB84Replace a k )
      )
    )
$.
