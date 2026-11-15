$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_33
  (verina__metamath__verina_basic_33), catalog title smallestMissingNumber:
  the exact executable recursive scan of a nondecreasing finite natural-number
  list returns the least natural number absent from that list. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite Lean lists of natural numbers. For a word w,
  # ` w is its length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB33State pairs the current candidate with a Boolean flag that records
  whether the recursive helper is still scanning. VERINAB33Step exactly
  implements one source match branch: an inactive state is unchanged; while
  active, an entry greater than the candidate returns that candidate and
  halts, an equal entry increments the candidate and continues, and a smaller
  entry leaves the candidate unchanged and continues.

  VERINAB33FindGraph records every state of this deterministic left-to-right
  execution, beginning with the supplied candidate. Retaining a halted state
  through the unused suffix gives exactly the value returned by the source's
  early recursive return. VERINAB33FindMissing selects the unique final
  candidate, and VERINAB33SmallestMissingNumber starts the helper at zero.
  Thus the executable result is fixed independently of the postcondition and
  admits no additional outputs.

  VERINAB33Pre is exactly List.Pairwise (fun x y => x <= y): every earlier
  list entry is at most every later entry. VERINAB33Elem is exact finite-list
  membership. VERINAB33Post states that the result is absent and every
  smaller natural number is present. The proof-valued precondition arguments
  to the implementation and postcondition are computationally and
  propositionally unused and are represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB33State VERINAB33Step
  VERINAB33FindGraph VERINAB33FindMissing
  VERINAB33Elem VERINAB33Pre
  VERINAB33SmallestMissingNumber VERINAB33Post
$.

verinab33-state-syntax
  $a class VERINAB33State $.
verinab33-step-syntax
  $a class ( VERINAB33Step A B ) $.
verinab33-find-graph-syntax
  $a wff ( VERINAB33FindGraph A B C ) $.
verinab33-find-missing-syntax
  $a class ( VERINAB33FindMissing A B ) $.
verinab33-elem-syntax
  $a wff ( VERINAB33Elem A B ) $.
verinab33-precondition-syntax
  $a wff ( VERINAB33Pre A ) $.
verinab33-program-syntax
  $a class ( VERINAB33SmallestMissingNumber A ) $.
verinab33-postcondition-syntax
  $a wff ( VERINAB33Post A B ) $.

verinab33-state-definition $a |- VERINAB33State = (
  NN0 X. { 0 , 1 }
) $.

verinab33-step-definition $a |- (
  VERINAB33Step A B
) = if (
  ( 2nd ` B ) = 0 ,
  B ,
  if (
    ( 1st ` B ) < A ,
    <. ( 1st ` B ) , 0 >. ,
    if (
      A = ( 1st ` B ) ,
      <. ( ( 1st ` B ) + 1 ) , 1 >. ,
      B
    )
  )
) $.

${
  $d k t A B C $.

  verinab33-find-graph-definition $a |- (
    VERINAB33FindGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. Word NN0
      )
      /\
      C e. NN0
    )
    /\
    E. t e. Word VERINAB33State
      (
        (
          ( # ` t ) = ( ( # ` B ) + 1 )
          /\
          ( t ` 0 ) = <. A , 1 >.
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` B ) )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB33Step
                ( B ` k )
                ( t ` k )
            )
          /\
          C = ( 1st ` ( t ` ( # ` B ) ) )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab33-find-missing-definition $a |- (
    VERINAB33FindMissing A B
  ) = (
    iota_ y e. NN0
      ( VERINAB33FindGraph A B y )
  ) $.
$}

${
  $d i A B $.

  verinab33-elem-definition $a |- (
    VERINAB33Elem A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      ( A ` i ) = B
  ) $.
$}

${
  $d i j A $.

  verinab33-precondition-definition $a |- (
    VERINAB33Pre A
  ) <-> (
    A e. Word NN0
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) <_ ( A ` j )
        )
  ) $.
$}

verinab33-program-definition $a |- (
  VERINAB33SmallestMissingNumber A
) = (
  VERINAB33FindMissing 0 A
) $.

${
  $d k A B $.

  verinab33-postcondition-definition $a |- (
    VERINAB33Post A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    (
      -. ( VERINAB33Elem A B )
      /\
      A. k e. NN0
        (
          k < B
          ->
          ( VERINAB33Elem A k )
        )
    )
  ) $.
$}

verina-basic-33-smallest-missing-number $a |- A. s e. Word NN0
  (
    ( VERINAB33Pre s )
    ->
    (
      VERINAB33Post
        s
        ( VERINAB33SmallestMissingNumber s )
    )
  )
$.
