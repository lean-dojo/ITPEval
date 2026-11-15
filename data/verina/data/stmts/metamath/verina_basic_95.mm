$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_95
  (verina__metamath__verina_basic_95), catalog title swap: the exact
  executable integer-array program exchanges the entries at two nonnegative
  in-bounds integer indices and satisfies the size, exchanged-entry, and
  unchanged-other-entry correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB95ToNat is exactly Lean Int.toNat, returning zero on negative
  integers. VERINAB95GetBang reproduces Lean Array.get! on integer arrays,
  including its inhabited default value zero outside the array.
  VERINAB95SetBangGraph and its iota-selected function reproduce Array.set!,
  including unchanged-array behavior at an out-of-range index.

  VERINAB95Swap preserves the source computation exactly. It converts both
  integer indices with Int.toNat, sets the first position to the original
  value at the second position, and then sets the second position of that
  intermediate array to the original value at the first position.

  VERINAB95Pre preserves the typed inputs, nonnegativity of both integer
  indices, and both converted-index bounds. VERINAB95Post preserves the
  result-size equation, both exchanged get! equations, and the universal
  unchanged-entry clause over every natural index. The proof-valued
  precondition arguments to the implementation and postcondition have no
  computational or propositional effect beyond the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB95ToNat VERINAB95GetBang
  VERINAB95SetBangGraph VERINAB95SetBang
  VERINAB95Pre VERINAB95Swap VERINAB95Post
$.

verinab95-to-nat-syntax
  $a class ( VERINAB95ToNat A ) $.
verinab95-get-bang-syntax
  $a class ( VERINAB95GetBang A B ) $.
verinab95-set-bang-graph-syntax
  $a wff ( VERINAB95SetBangGraph A B C D ) $.
verinab95-set-bang-syntax
  $a class ( VERINAB95SetBang A B C ) $.
verinab95-precondition-syntax
  $a wff ( VERINAB95Pre A B C ) $.
verinab95-program-syntax
  $a class ( VERINAB95Swap A B C ) $.
verinab95-postcondition-syntax
  $a wff ( VERINAB95Post A B C D ) $.

verinab95-to-nat-definition $a |- (
  VERINAB95ToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

verinab95-get-bang-definition $a |- (
  VERINAB95GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab95-set-bang-graph-definition $a |- (
    VERINAB95SetBangGraph A B C D
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

  verinab95-set-bang-definition $a |- (
    VERINAB95SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB95SetBangGraph A B C y )
  ) $.
$}

verinab95-precondition-definition $a |- (
  VERINAB95Pre A B C
) <-> (
  (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    C e. ZZ
  )
  /\
  (
    0 <_ B
    /\
    (
      0 <_ C
      /\
      (
        ( VERINAB95ToNat B ) < ( # ` A )
        /\
        ( VERINAB95ToNat C ) < ( # ` A )
      )
    )
  )
) $.

verinab95-program-definition $a |- (
  VERINAB95Swap A B C
) = (
  VERINAB95SetBang
    (
      VERINAB95SetBang
        A
        ( VERINAB95ToNat B )
        (
          VERINAB95GetBang
            A
            ( VERINAB95ToNat C )
        )
    )
    ( VERINAB95ToNat C )
    (
      VERINAB95GetBang
        A
        ( VERINAB95ToNat B )
    )
) $.

${
  $d k A B C D $.

  verinab95-postcondition-definition $a |- (
    VERINAB95Post A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. ZZ
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
      (
        (
          VERINAB95GetBang D ( VERINAB95ToNat B )
        ) = (
          VERINAB95GetBang A ( VERINAB95ToNat C )
        )
        /\
        (
          (
            VERINAB95GetBang D ( VERINAB95ToNat C )
          ) = (
            VERINAB95GetBang A ( VERINAB95ToNat B )
          )
          /\
          A. k e. NN0
            (
              (
                (
                  k < ( # ` A )
                  /\
                  k =/= ( VERINAB95ToNat B )
                )
                /\
                k =/= ( VERINAB95ToNat C )
              )
              ->
              (
                VERINAB95GetBang D k
              ) = (
                VERINAB95GetBang A k
              )
            )
        )
      )
    )
  ) $.
$}

verina-basic-95-swap $a |- A. a e. Word ZZ
  A. i e. ZZ
    A. j e. ZZ
      (
        ( VERINAB95Pre a i j )
        ->
        (
          VERINAB95Post
            a
            i
            j
            ( VERINAB95Swap a i j )
        )
      )
$.
