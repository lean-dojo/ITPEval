$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_58
  (verina__metamath__verina_basic_58), catalog title
  double_array_elements: the exact executable recursive integer-array program
  doubles every entry of an arbitrary finite array and satisfies its
  size-and-pointwise-doubling correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ n is the set of natural indices below n.

  VERINAB58NatSub is Lean's truncated natural subtraction.
  VERINAB58GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB58SetBangGraph
  and its iota-selected function reproduce Array.set!, including unchanged
  array behavior at an out-of-range index.

  VERINAB58AuxGraph is the exact finite execution trace of the source
  double_array_elements_aux helper for every immutable old array, current
  array, and natural starting index. It has max(current.size - i, 0)
  transitions. Transition k writes index i + k of the current state with
  twice get! at index i + k of the immutable old array. Since set! preserves
  the current size, this is exactly the source guard and recursive call.
  VERINAB58Aux selects the unique final array fixed by that trace, and
  VERINAB58DoubleArrayElements invokes it with the input as both array
  arguments and starting index zero.

  VERINAB58Pre is the source True precondition on typed Array Int inputs.
  VERINAB58Post preserves the result-size equation and the universal
  pointwise doubling equation at every valid input index. The proof-valued
  precondition arguments to the implementation and postcondition are
  computationally and propositionally unused and are represented by the
  explicit precondition antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB58NatSub VERINAB58GetBang
  VERINAB58SetBangGraph VERINAB58SetBang
  VERINAB58AuxGraph VERINAB58Aux
  VERINAB58Pre VERINAB58DoubleArrayElements VERINAB58Post
$.

verinab58-nat-sub-syntax
  $a class ( VERINAB58NatSub A B ) $.
verinab58-get-bang-syntax
  $a class ( VERINAB58GetBang A B ) $.
verinab58-set-bang-graph-syntax
  $a wff ( VERINAB58SetBangGraph A B C D ) $.
verinab58-set-bang-syntax
  $a class ( VERINAB58SetBang A B C ) $.
verinab58-aux-graph-syntax
  $a wff ( VERINAB58AuxGraph A B C D ) $.
verinab58-aux-syntax
  $a class ( VERINAB58Aux A B C ) $.
verinab58-precondition-syntax
  $a wff ( VERINAB58Pre A ) $.
verinab58-program-syntax
  $a class ( VERINAB58DoubleArrayElements A ) $.
verinab58-postcondition-syntax
  $a wff ( VERINAB58Post A B ) $.

verinab58-nat-sub-definition $a |- (
  VERINAB58NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab58-get-bang-definition $a |- (
  VERINAB58GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i A B C D $.

  verinab58-set-bang-graph-definition $a |- (
    VERINAB58SetBangGraph A B C D
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

  verinab58-set-bang-definition $a |- (
    VERINAB58SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB58SetBangGraph A B C y )
  ) $.
$}

${
  $d k t A B C D $.

  verinab58-aux-graph-definition $a |- (
    VERINAB58AuxGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. Word ZZ
        )
        /\
        C e. NN0
      )
      /\
      D e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = (
            ( VERINAB58NatSub ( # ` B ) C ) + 1
          )
          /\
          ( t ` 0 ) = B
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB58NatSub ( # ` B ) C )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB58SetBang
                ( t ` k )
                ( C + k )
                (
                  2 x. (
                    VERINAB58GetBang A ( C + k )
                  )
                )
            )
          /\
          D = (
            t ` ( VERINAB58NatSub ( # ` B ) C )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab58-aux-definition $a |- (
    VERINAB58Aux A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB58AuxGraph A B C y )
  ) $.
$}

verinab58-precondition-definition $a |- (
  VERINAB58Pre A
) <-> (
  A e. Word ZZ
) $.

verinab58-program-definition $a |- (
  VERINAB58DoubleArrayElements A
) = (
  VERINAB58Aux A A 0
) $.

${
  $d i A B $.

  verinab58-postcondition-definition $a |- (
    VERINAB58Post A B
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
            VERINAB58GetBang B i
          ) = (
            2 x. ( VERINAB58GetBang A i )
          )
        )
    )
  ) $.
$}

verina-basic-58-double-array-elements $a |- A. w e. Word ZZ
  (
    ( VERINAB58Pre w )
    ->
    (
      VERINAB58Post
        w
        ( VERINAB58DoubleArrayElements w )
    )
  )
$.
