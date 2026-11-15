$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_74
  (verina__metamath__verina_basic_74), catalog title maxArray: the exact
  executable recursive scan of a nonempty finite integer array returns an
  array element that is greater than or equal to every entry. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB74GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB74NatSub is
  Lean's truncated natural subtraction. VERINAB74MaxStep is exactly the
  source conditional: retain current when it is strictly greater than the
  next entry, and otherwise take that entry.

  VERINAB74AuxGraph is the complete finite execution trace of maxArray_aux
  for every integer array, natural starting index, and integer accumulator.
  The trace starts at current and has one transition for each remaining
  in-bounds index. Transition k reads get! a (index + k), performs the exact
  source maximum update, and the graph returns the final accumulator. If the
  starting index is at or beyond the array size, the trace has no transition
  and returns current. VERINAB74Aux selects this unique result.

  VERINAB74Pre preserves the nonempty Array Int precondition.
  VERINAB74MaxArray is exactly the executable source call maxArray_aux a 1
  a[0]!. VERINAB74Post preserves both source clauses: the result is at least
  every valid get! entry and equals some valid get! entry. The proof-valued
  precondition arguments have no computational effect and the postcondition
  body does not inspect them, so the final correctness assertion represents
  them by its explicit precondition antecedent. Every earlier $a is syntax or
  a faithful definition required by this rendering, and this database has no
  $p declaration.
$)

$c
  VERINAB74GetBang VERINAB74NatSub VERINAB74MaxStep
  VERINAB74AuxGraph VERINAB74Aux
  VERINAB74Pre VERINAB74MaxArray VERINAB74Post
$.

verinab74-get-bang-syntax
  $a class ( VERINAB74GetBang A B ) $.
verinab74-nat-sub-syntax
  $a class ( VERINAB74NatSub A B ) $.
verinab74-max-step-syntax
  $a class ( VERINAB74MaxStep A B ) $.
verinab74-aux-graph-syntax
  $a wff ( VERINAB74AuxGraph A B C D ) $.
verinab74-aux-syntax
  $a class ( VERINAB74Aux A B C ) $.
verinab74-precondition-syntax
  $a wff ( VERINAB74Pre A ) $.
verinab74-program-syntax
  $a class ( VERINAB74MaxArray A ) $.
verinab74-postcondition-syntax
  $a wff ( VERINAB74Post A B ) $.

verinab74-get-bang-definition $a |- (
  VERINAB74GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab74-nat-sub-definition $a |- (
  VERINAB74NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab74-max-step-definition $a |- (
  VERINAB74MaxStep A B
) = if (
  B < A ,
  A ,
  B
) $.

${
  $d k t A B C D $.

  verinab74-aux-graph-definition $a |- (
    VERINAB74AuxGraph A B C D
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
      D e. ZZ
    )
    /\
    E. t e. Word ZZ
      (
        (
          ( # ` t ) = (
            ( VERINAB74NatSub ( # ` A ) B ) + 1
          )
          /\
          ( t ` 0 ) = C
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB74NatSub ( # ` A ) B )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB74MaxStep
                ( t ` k )
                ( VERINAB74GetBang A ( B + k ) )
            )
          /\
          D = (
            t ` ( VERINAB74NatSub ( # ` A ) B )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab74-aux-definition $a |- (
    VERINAB74Aux A B C
  ) = (
    iota_ y e. ZZ
      ( VERINAB74AuxGraph A B C y )
  ) $.
$}

verinab74-precondition-definition $a |- (
  VERINAB74Pre A
) <-> (
  A e. Word ZZ
  /\
  0 < ( # ` A )
) $.

verinab74-program-definition $a |- (
  VERINAB74MaxArray A
) = (
  VERINAB74Aux
    A
    1
    ( VERINAB74GetBang A 0 )
) $.

${
  $d k A B $.

  verinab74-postcondition-definition $a |- (
    VERINAB74Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      A. k e. ( 0 ..^ ( # ` A ) )
        ( VERINAB74GetBang A k ) <_ B
      /\
      E. k e. ( 0 ..^ ( # ` A ) )
        B = ( VERINAB74GetBang A k )
    )
  ) $.
$}

verina-basic-74-max-array $a |- A. a e. Word ZZ
  (
    ( VERINAB74Pre a )
    ->
    (
      VERINAB74Post
        a
        ( VERINAB74MaxArray a )
    )
  )
$.
