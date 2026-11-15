$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_97
  (verina__metamath__verina_basic_97), catalog title TestArrayElements: the
  exact executable integer-array program sets the entry at an in-bounds
  natural-number index to 60 and satisfies the complete size, updated-entry,
  and unchanged-other-entry correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB97GetBang reproduces Lean Array.get! on integer arrays, including its
  inhabited default value zero outside the array. VERINAB97SetBangGraph and
  its iota-selected function reproduce Array.set!, including unchanged-array
  behavior at an out-of-range index. VERINAB97TestArrayElements is exactly the
  source executable call a.set! j 60.

  VERINAB97Pre preserves the Array Int and Nat input types and the source
  in-bounds precondition. VERINAB97Post preserves the result-size equation,
  the updated get! equation, and the universal unchanged-entry clause over
  every natural index. The proof-valued precondition arguments to the
  implementation and postcondition have no computational or propositional
  effect beyond the explicit precondition antecedent in the final correctness
  assertion. Every earlier $a is syntax or a faithful definition required by
  this rendering, and this database has no $p declaration.
$)

$c
  VERINAB97GetBang
  VERINAB97SetBangGraph VERINAB97SetBang
  VERINAB97Pre VERINAB97TestArrayElements VERINAB97Post
$.

verinab97-get-bang-syntax
  $a class ( VERINAB97GetBang A B ) $.
verinab97-set-bang-graph-syntax
  $a wff ( VERINAB97SetBangGraph A B C D ) $.
verinab97-set-bang-syntax
  $a class ( VERINAB97SetBang A B C ) $.
verinab97-precondition-syntax
  $a wff ( VERINAB97Pre A B ) $.
verinab97-program-syntax
  $a class ( VERINAB97TestArrayElements A B ) $.
verinab97-postcondition-syntax
  $a wff ( VERINAB97Post A B C ) $.

verinab97-get-bang-definition $a |- (
  VERINAB97GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab97-set-bang-graph-definition $a |- (
    VERINAB97SetBangGraph A B C D
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

  verinab97-set-bang-definition $a |- (
    VERINAB97SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB97SetBangGraph A B C y )
  ) $.
$}

verinab97-precondition-definition $a |- (
  VERINAB97Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. NN0
  )
  /\
  B < ( # ` A )
) $.

verinab97-program-definition $a |- (
  VERINAB97TestArrayElements A B
) = (
  VERINAB97SetBang A B ; 6 0
) $.

${
  $d k A B C $.

  verinab97-postcondition-definition $a |- (
    VERINAB97Post A B C
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
    (
      ( # ` C ) = ( # ` A )
      /\
      (
        ( VERINAB97GetBang C B ) = ; 6 0
        /\
        A. k e. NN0
          (
            (
              k < ( # ` A )
              /\
              k =/= B
            )
            ->
            (
              ( VERINAB97GetBang C k )
              =
              ( VERINAB97GetBang A k )
            )
          )
      )
    )
  ) $.
$}

verina-basic-97-test-array-elements $a |- A. a e. Word ZZ
  A. j e. NN0
    (
      ( VERINAB97Pre a j )
      ->
      (
        VERINAB97Post
          a
          j
          ( VERINAB97TestArrayElements a j )
      )
    )
$.
