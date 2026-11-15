$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_80
  (verina__metamath__verina_basic_80), catalog title only_once: the exact
  executable left-to-right scan of a finite integer array returns true
  exactly when the selected key occurs once, together with its complete
  precondition and Boolean correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word S is exactly the type of arbitrary finite arrays over an arbitrary
  set S. For a word w, # ` w is its natural-number size, w ` k is zero-based
  lookup, and 0 ..^ n is the natural index set below n. The Boolean domain is
  { 0 , 1 }, with false = 0 and true = 1.

  VERINAB80NatSub is Lean's truncated natural subtraction.
  VERINAB80LoopGraph preserves the polymorphic only_once_loop helper for every
  element set, finite array, key, natural starting index, and natural initial
  count. Its natural-number trace has one state before each remaining array
  entry and a final state. Each transition increments exactly when the
  current entry equals the key. The returned Boolean is true exactly when
  the final count is one. If the starting index is at or beyond the array
  size, the trace has no transitions and tests the supplied count directly,
  exactly as the source guard does. Because an in-bounds word lookup always
  exists, the source get? none branch is unreachable. VERINAB80OnlyOnceLoop
  selects the unique result of this deterministic trace.

  VERINAB80Pre is the source True precondition together with the Array Int
  and Int input types. VERINAB80OnlyOnce invokes the exact generic loop at
  integer type, index zero, and count zero. VERINAB80CountOccurrences is the
  cardinality of all valid indices containing the key, which is exactly the
  source foldl from zero that increments on equality.

  VERINAB80Post preserves both source implications: count one implies a true
  result, while any other count implies a false result. The proof-valued
  precondition arguments to the implementation and postcondition are
  computationally and propositionally unused beyond the explicit
  precondition antecedent in the final correctness assertion. Every earlier
  $a is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB80NatSub
  VERINAB80LoopGraph VERINAB80OnlyOnceLoop
  VERINAB80Pre VERINAB80OnlyOnce
  VERINAB80CountOccurrences VERINAB80Post
$.

verinab80-nat-sub-syntax
  $a class ( VERINAB80NatSub A B ) $.
verinab80-loop-graph-syntax
  $a wff ( VERINAB80LoopGraph A B C D E F ) $.
verinab80-loop-syntax
  $a class ( VERINAB80OnlyOnceLoop A B C D E ) $.
verinab80-precondition-syntax
  $a wff ( VERINAB80Pre A B ) $.
verinab80-program-syntax
  $a class ( VERINAB80OnlyOnce A B ) $.
verinab80-count-occurrences-syntax
  $a class ( VERINAB80CountOccurrences A B C ) $.
verinab80-postcondition-syntax
  $a wff ( VERINAB80Post A B C ) $.

verinab80-nat-sub-definition $a |- (
  VERINAB80NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d k s A B C D E F $.

  verinab80-loop-graph-definition $a |- (
    VERINAB80LoopGraph A B C D E F
  ) <-> (
    (
      (
        (
          (
            (
              A e. _V
              /\
              B e. Word A
            )
            /\
            C e. A
          )
          /\
          D e. NN0
        )
        /\
        E e. NN0
      )
      /\
      F e. { 0 , 1 }
    )
    /\
    E. s e. Word NN0
      (
        (
          (
            # ` s
          ) = (
            (
              VERINAB80NatSub
                ( # ` B )
                D
            ) + 1
          )
          /\
          ( s ` 0 ) = E
        )
        /\
        (
          A. k e. (
            0 ..^ (
              VERINAB80NatSub
                ( # ` B )
                D
            )
          )
            (
              s ` ( k + 1 )
            ) = if (
              ( B ` ( D + k ) ) = C ,
              ( ( s ` k ) + 1 ) ,
              ( s ` k )
            )
          /\
          F = if (
            (
              s ` (
                VERINAB80NatSub
                  ( # ` B )
                  D
              )
            ) = 1 ,
            1 ,
            0
          )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verinab80-loop-definition $a |- (
    VERINAB80OnlyOnceLoop A B C D E
  ) = (
    iota_ y e. { 0 , 1 }
      (
        VERINAB80LoopGraph
          A B C D E y
      )
  ) $.
$}

verinab80-precondition-definition $a |- (
  VERINAB80Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. ZZ
) $.

verinab80-program-definition $a |- (
  VERINAB80OnlyOnce A B
) = (
  VERINAB80OnlyOnceLoop
    ZZ
    A
    B
    0
    0
) $.

${
  $d k A B C $.

  verinab80-count-occurrences-definition $a |- (
    VERINAB80CountOccurrences A B C
  ) = (
    # ` {
      k e. ( 0 ..^ ( # ` B ) )
      |
      ( B ` k ) = C
    }
  ) $.
$}

verinab80-postcondition-definition $a |- (
  VERINAB80Post A B C
) <-> (
  (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    C e. { 0 , 1 }
  )
  /\
  (
    (
      (
        VERINAB80CountOccurrences
          ZZ
          A
          B
      ) = 1
      ->
      C = 1
    )
    /\
    (
      (
        VERINAB80CountOccurrences
          ZZ
          A
          B
      ) =/= 1
      ->
      C = 0
    )
  )
) $.

verina-basic-80-only-once $a |-
  A. a e. Word ZZ
    A. k e. ZZ
      (
        ( VERINAB80Pre a k )
        ->
        (
          VERINAB80Post
            a
            k
            ( VERINAB80OnlyOnce a k )
        )
      )
$.
