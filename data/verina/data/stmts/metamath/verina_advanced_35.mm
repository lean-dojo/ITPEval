$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_35 (verina__metamath__verina_advanced_35), catalog title
  majorityElement: the exact hash-map counting program returns the unique
  integer occurring more than half the length of an arbitrary nonempty
  finite integer list, with the stated majority and uniqueness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set. VERINA35Count is List.count.
  The floor expression is Lean's natural-number division by two.

  VERINA35CountsGraph is the exact finite execution trace of the source
  mutable HashMap loop. Row k records getD values after the first k input
  entries have been inserted, for every integer key that occurs in the
  input. The initial row is zero, and processing input[k] increments exactly
  the slots representing that same integer. Thus its final row is the
  source map extensionally on every stored key; absent keys have getD value
  zero and are irrelevant to toList.

  VERINA35SearchGraph reproduces counts.toList.find? followed by the source
  default zero. A strict majority key is unique, so HashMap bucket and toList
  order cannot affect the selected key; if no strict majority exists, every
  stored key fails the test and the result is zero. VERINA35ProgramGraph
  composes this search with the counting trace, and VERINA35MajorityElement
  selects its unique result. The implementation is therefore determined by
  the source computation, not by the postcondition.

  VERINA35Pre is exactly the positive-length conjunction with List.any of a
  value whose List.count exceeds floor(length / 2). VERINA35Post is exactly
  the returned-value count bound and the universal bound for every unequal
  input element. The proof-valued precondition argument is computationally
  and propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database has
  no $p declaration.
$)

$c
  VERINA35Count
  VERINA35CountsGraph
  VERINA35SearchGraph
  VERINA35ProgramGraph VERINA35MajorityElement
  VERINA35Pre VERINA35Post
$.

verina35-count-syntax
  $a class ( VERINA35Count A B ) $.
verina35-counts-graph-syntax
  $a wff ( VERINA35CountsGraph A B ) $.
verina35-search-graph-syntax
  $a wff ( VERINA35SearchGraph A B C ) $.
verina35-program-graph-syntax
  $a wff ( VERINA35ProgramGraph A B ) $.
verina35-majority-element-syntax
  $a class ( VERINA35MajorityElement A ) $.
verina35-precondition-syntax
  $a wff ( VERINA35Pre A ) $.
verina35-postcondition-syntax
  $a wff ( VERINA35Post A B ) $.

${
  $d i A B $.

  verina35-count-definition $a |- (
    VERINA35Count A B
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( A ` i ) = B
    }
  ) $.
$}

${
  $d j k t A B $.

  verina35-counts-graph-definition $a |- (
    VERINA35CountsGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word NN0
    )
    /\
    E. t e. Word ( Word NN0 )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          A. k e. ( 0 ..^ ( # ` t ) )
            ( # ` ( t ` k ) ) = ( # ` A )
        )
        /\
        (
          A. j e. ( 0 ..^ ( # ` A ) )
            ( ( t ` 0 ) ` j ) = 0
          /\
          (
            A. k e. ( 0 ..^ ( # ` A ) )
              A. j e. ( 0 ..^ ( # ` A ) )
                (
                  ( t ` ( k + 1 ) ) ` j
                ) = if (
                  ( A ` j ) = ( A ` k ) ,
                  ( ( ( t ` k ) ` j ) + 1 ) ,
                  ( ( t ` k ) ` j )
                )
            /\
            B = ( t ` ( # ` A ) )
          )
        )
      )
  ) $.
$}

${
  $d i A B C $.

  verina35-search-graph-definition $a |- (
    VERINA35SearchGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word NN0
      )
      /\
      C e. ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      (
        E. i e. ( 0 ..^ ( # ` A ) )
          (
            (
              |_ ` ( ( # ` A ) / 2 )
            ) < ( B ` i )
            /\
            C = ( A ` i )
          )
        \/
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            ( B ` i ) <_ (
              |_ ` ( ( # ` A ) / 2 )
            )
          /\
          C = 0
        )
      )
    )
  ) $.
$}

${
  $d q A B $.

  verina35-program-graph-definition $a |- (
    VERINA35ProgramGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. q e. Word NN0
      (
        ( VERINA35CountsGraph A q )
        /\
        ( VERINA35SearchGraph A q B )
      )
  ) $.
$}

${
  $d y A $.

  verina35-majority-element-definition $a |- (
    VERINA35MajorityElement A
  ) = (
    iota_ y e. ZZ
      ( VERINA35ProgramGraph A y )
  ) $.
$}

${
  $d i A $.

  verina35-precondition-definition $a |- (
    VERINA35Pre A
  ) <-> (
    (
      A e. Word ZZ
      /\
      0 < ( # ` A )
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      (
        |_ ` ( ( # ` A ) / 2 )
      ) < (
        VERINA35Count A ( A ` i )
      )
  ) $.
$}

${
  $d i A B $.

  verina35-postcondition-definition $a |- (
    VERINA35Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      (
        |_ ` ( ( # ` A ) / 2 )
      ) < (
        VERINA35Count A B
      )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          ( A ` i ) =/= B
          ->
          (
            VERINA35Count A ( A ` i )
          ) <_ (
            |_ ` ( ( # ` A ) / 2 )
          )
        )
    )
  ) $.
$}

verina-advanced-35-majority-element
  $a |- A. w e. Word ZZ
    (
      ( VERINA35Pre w )
      ->
      (
        VERINA35Post
          w
          ( VERINA35MajorityElement w )
      )
    )
  $.
