$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_57
  (verina__metamath__verina_basic_57), catalog title CountLessThan: the exact
  executable integer-array scan counts entries below an arbitrary integer
  threshold and satisfies its independently folded counting contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ n is the set of natural indices below n.

  VERINAB57NatSub is Lean's truncated natural subtraction.
  VERINAB57CountGraph is the exact finite execution graph of the source local
  recursive count helper for every natural starting index and accumulator.
  The number of loop iterations is array-size minus the starting index,
  truncated at zero. Each transition examines the next in-bounds integer and
  increments the natural accumulator exactly when that integer is below the
  threshold. VERINAB57Count selects the unique final accumulator.
  VERINAB57CountLessThan invokes that helper at index zero with accumulator
  zero, exactly as the source executable implementation does.

  VERINAB57FoldGraph separately records every accumulator of the source
  Array.foldl in left-to-right order, and VERINAB57Fold selects its unique
  final value. VERINAB57Pre is the source True precondition on typed inputs.
  VERINAB57Post preserves literally the two source truncated-subtraction
  equations between the result and the fold count.

  The proof-valued precondition arguments to the implementation and
  postcondition are computationally and propositionally unused and are
  represented by the explicit precondition antecedent in the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c
  VERINAB57NatSub
  VERINAB57CountGraph VERINAB57Count
  VERINAB57Pre VERINAB57CountLessThan
  VERINAB57FoldGraph VERINAB57Fold
  VERINAB57Post
$.

verinab57-nat-sub-syntax
  $a class ( VERINAB57NatSub A B ) $.
verinab57-count-graph-syntax
  $a wff ( VERINAB57CountGraph A B C D E ) $.
verinab57-count-syntax
  $a class ( VERINAB57Count A B C D ) $.
verinab57-precondition-syntax
  $a wff ( VERINAB57Pre A B ) $.
verinab57-program-syntax
  $a class ( VERINAB57CountLessThan A B ) $.
verinab57-fold-graph-syntax
  $a wff ( VERINAB57FoldGraph A B C ) $.
verinab57-fold-syntax
  $a class ( VERINAB57Fold A B ) $.
verinab57-postcondition-syntax
  $a wff ( VERINAB57Post A B C ) $.

verinab57-nat-sub-definition $a |- (
  VERINAB57NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d k s A B C D E $.

  verinab57-count-graph-definition $a |- (
    VERINAB57CountGraph A B C D E
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
        D e. NN0
      )
      /\
      E e. NN0
    )
    /\
    E. s e. Word NN0
      (
        (
          (
            # ` s
          ) = (
            (
              VERINAB57NatSub
                ( # ` A )
                C
            ) + 1
          )
          /\
          ( s ` 0 ) = D
        )
        /\
        (
          A. k e. (
            0 ..^ (
              VERINAB57NatSub
                ( # ` A )
                C
            )
          )
            (
              s ` ( k + 1 )
            ) = if (
              ( A ` ( C + k ) ) < B ,
              ( ( s ` k ) + 1 ) ,
              ( s ` k )
            )
          /\
          E = (
            s ` (
              VERINAB57NatSub
                ( # ` A )
                C
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D $.

  verinab57-count-definition $a |- (
    VERINAB57Count A B C D
  ) = (
    iota_ y e. NN0
      ( VERINAB57CountGraph A B C D y )
  ) $.
$}

verinab57-precondition-definition $a |- (
  VERINAB57Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. ZZ
) $.

verinab57-program-definition $a |- (
  VERINAB57CountLessThan A B
) = (
  VERINAB57Count A B 0 0
) $.

${
  $d k s A B C $.

  verinab57-fold-graph-definition $a |- (
    VERINAB57FoldGraph A B C
  ) <-> (
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
    E. s e. Word NN0
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( k + 1 )
            ) = if (
              ( A ` k ) < B ,
              ( ( s ` k ) + 1 ) ,
              ( s ` k )
            )
          /\
          C = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab57-fold-definition $a |- (
    VERINAB57Fold A B
  ) = (
    iota_ y e. NN0
      ( VERINAB57FoldGraph A B y )
  ) $.
$}

verinab57-postcondition-definition $a |- (
  VERINAB57Post A B C
) <-> (
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
  (
    (
      VERINAB57NatSub
        C
        ( VERINAB57Fold A B )
    ) = 0
    /\
    (
      VERINAB57NatSub
        ( VERINAB57Fold A B )
        C
    ) = 0
  )
) $.

verina-basic-57-count-less-than $a |- A. w e. Word ZZ
  A. z e. ZZ
    (
      ( VERINAB57Pre w z )
      ->
      (
        VERINAB57Post
          w
          z
          ( VERINAB57CountLessThan w z )
      )
    )
$.
