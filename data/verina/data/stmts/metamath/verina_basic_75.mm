$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_75
  (verina__metamath__verina_basic_75), catalog title minArray: the exact
  executable recursive scan of a nonempty finite integer array returns an
  array element that is less than or equal to every entry. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB75GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB75NatSub is
  Lean's truncated natural subtraction. VERINAB75MinStep is exactly the
  source conditional: replace current by the next entry when current is
  strictly greater, and otherwise retain current.

  VERINAB75LoopGraph is the complete finite execution trace of loop for every
  integer array, natural starting index, and integer accumulator. The trace
  starts at current and has one transition for each remaining in-bounds
  index. Transition k reads get! a (i + k), performs the exact source minimum
  update, and the graph returns the final accumulator. If the starting index
  is at or beyond the array size, the trace has no transition and returns
  current. VERINAB75Loop selects this unique result.

  VERINAB75Pre preserves the nonempty Array Int precondition.
  VERINAB75MinArray is exactly the executable source call loop a 1 a[0]!.
  VERINAB75Post preserves both source clauses: the result is at most every
  valid get! entry and equals some valid get! entry. The proof-valued
  precondition arguments have no computational effect and the postcondition
  body does not inspect them, so the final correctness assertion represents
  them by its explicit precondition antecedent. Every earlier $a is syntax or
  a faithful definition required by this rendering, and this database has no
  $p declaration.
$)

$c
  VERINAB75GetBang VERINAB75NatSub VERINAB75MinStep
  VERINAB75LoopGraph VERINAB75Loop
  VERINAB75Pre VERINAB75MinArray VERINAB75Post
$.

verinab75-get-bang-syntax
  $a class ( VERINAB75GetBang A B ) $.
verinab75-nat-sub-syntax
  $a class ( VERINAB75NatSub A B ) $.
verinab75-min-step-syntax
  $a class ( VERINAB75MinStep A B ) $.
verinab75-loop-graph-syntax
  $a wff ( VERINAB75LoopGraph A B C D ) $.
verinab75-loop-syntax
  $a class ( VERINAB75Loop A B C ) $.
verinab75-precondition-syntax
  $a wff ( VERINAB75Pre A ) $.
verinab75-program-syntax
  $a class ( VERINAB75MinArray A ) $.
verinab75-postcondition-syntax
  $a wff ( VERINAB75Post A B ) $.

verinab75-get-bang-definition $a |- (
  VERINAB75GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab75-nat-sub-definition $a |- (
  VERINAB75NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab75-min-step-definition $a |- (
  VERINAB75MinStep A B
) = if (
  B < A ,
  B ,
  A
) $.

${
  $d k t A B C D $.

  verinab75-loop-graph-definition $a |- (
    VERINAB75LoopGraph A B C D
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
            ( VERINAB75NatSub ( # ` A ) B ) + 1
          )
          /\
          ( t ` 0 ) = C
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB75NatSub ( # ` A ) B )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB75MinStep
                ( t ` k )
                ( VERINAB75GetBang A ( B + k ) )
            )
          /\
          D = (
            t ` ( VERINAB75NatSub ( # ` A ) B )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab75-loop-definition $a |- (
    VERINAB75Loop A B C
  ) = (
    iota_ y e. ZZ
      ( VERINAB75LoopGraph A B C y )
  ) $.
$}

verinab75-precondition-definition $a |- (
  VERINAB75Pre A
) <-> (
  A e. Word ZZ
  /\
  0 < ( # ` A )
) $.

verinab75-program-definition $a |- (
  VERINAB75MinArray A
) = (
  VERINAB75Loop
    A
    1
    ( VERINAB75GetBang A 0 )
) $.

${
  $d k A B $.

  verinab75-postcondition-definition $a |- (
    VERINAB75Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      A. k e. ( 0 ..^ ( # ` A ) )
        B <_ ( VERINAB75GetBang A k )
      /\
      E. k e. ( 0 ..^ ( # ` A ) )
        B = ( VERINAB75GetBang A k )
    )
  ) $.
$}

verina-basic-75-min-array $a |- A. a e. Word ZZ
  (
    ( VERINAB75Pre a )
    ->
    (
      VERINAB75Post
        a
        ( VERINAB75MinArray a )
    )
  )
$.
