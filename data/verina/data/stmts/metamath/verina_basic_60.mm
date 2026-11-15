$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_60
  (verina__metamath__verina_basic_60), catalog title FindEvenNumbers: the
  exact executable indexed integer-array loop retains every even entry in
  source order and satisfies its all-even, sublist, and count correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays and lists.
  For a word w, # ` w is its natural-number length, w ` i is zero-based
  lookup, 0 ..^ ( # ` w ) is its complete valid-index set, (/) is the empty
  word, <" x "> is a singleton word, and ++ is word concatenation.

  VERINAB60IsEven is the source Boolean helper isEven: it is one exactly when
  Lean's integer Euclidean remainder modulo two is zero, and zero otherwise.
  VERINAB60ToList is Array.toList extensionally. VERINAB60NatSub is truncated
  natural subtraction, and VERINAB60GetD reproduces arr.getD i 0, including
  its out-of-range zero default.

  VERINAB60LoopGraph records every accumulator of the source local recursive
  loop for an arbitrary natural starting index and arbitrary accumulator.
  It has arr.size - i transitions, truncated at zero. Transition k inspects
  getD at i + k and appends that value exactly when isEven returns true.
  VERINAB60Loop selects the unique final accumulator, and
  VERINAB60FindEvenNumbers invokes it at index zero with Array.mkEmpty 0,
  represented by the empty word. Thus the executable output is fixed
  independently of the postcondition and admits no additional results.

  VERINAB60AllEven is exactly the proposition obtained by coercing the source
  result.all Boolean to Prop. VERINAB60Sublist uses a strictly increasing word
  of source indices and is equivalent to Lean List.Sublist, preserving order
  and repeated occurrences. VERINAB60CountP is the cardinality of precisely
  those valid positions where isEven is true, exactly List.countP isEven.
  VERINAB60Pre is the source True precondition on typed Array Int inputs, and
  VERINAB60Post preserves the three source conjuncts without strengthening.

  The proof-valued precondition arguments to the implementation and
  postcondition are computationally and propositionally unused beyond the
  explicit precondition antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB60IsEven VERINAB60ToList
  VERINAB60NatSub VERINAB60GetD
  VERINAB60LoopGraph VERINAB60Loop
  VERINAB60Pre VERINAB60FindEvenNumbers
  VERINAB60AllEven VERINAB60Sublist VERINAB60CountP
  VERINAB60Post
$.

verinab60-is-even-syntax
  $a class ( VERINAB60IsEven A ) $.
verinab60-to-list-syntax
  $a class ( VERINAB60ToList A ) $.
verinab60-nat-sub-syntax
  $a class ( VERINAB60NatSub A B ) $.
verinab60-get-d-syntax
  $a class ( VERINAB60GetD A B ) $.
verinab60-loop-graph-syntax
  $a wff ( VERINAB60LoopGraph A B C D ) $.
verinab60-loop-syntax
  $a class ( VERINAB60Loop A B C ) $.
verinab60-precondition-syntax
  $a wff ( VERINAB60Pre A ) $.
verinab60-program-syntax
  $a class ( VERINAB60FindEvenNumbers A ) $.
verinab60-all-even-syntax
  $a wff ( VERINAB60AllEven A ) $.
verinab60-sublist-syntax
  $a wff ( VERINAB60Sublist A B ) $.
verinab60-count-p-syntax
  $a class ( VERINAB60CountP A ) $.
verinab60-postcondition-syntax
  $a wff ( VERINAB60Post A B ) $.

verinab60-is-even-definition $a |- (
  VERINAB60IsEven A
) = if (
  ( A mod 2 ) = 0 ,
  1 ,
  0
) $.

verinab60-to-list-definition $a |- (
  VERINAB60ToList A
) = A $.

verinab60-nat-sub-definition $a |- (
  VERINAB60NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab60-get-d-definition $a |- (
  VERINAB60GetD A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k t A B C D $.

  verinab60-loop-graph-definition $a |- (
    VERINAB60LoopGraph A B C D
  ) <-> (
    (
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
      D e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = (
            ( VERINAB60NatSub ( # ` A ) B ) + 1
          )
          /\
          ( t ` 0 ) = C
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB60NatSub ( # ` A ) B )
          )
            (
              t ` ( k + 1 )
            ) = if (
              (
                VERINAB60IsEven
                  ( VERINAB60GetD A ( B + k ) )
              ) = 1 ,
              (
                ( t ` k )
                ++
                <"
                  ( VERINAB60GetD A ( B + k ) )
                ">
              ) ,
              ( t ` k )
            )
          /\
          D = (
            t ` ( VERINAB60NatSub ( # ` A ) B )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab60-loop-definition $a |- (
    VERINAB60Loop A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB60LoopGraph A B C y )
  ) $.
$}

verinab60-precondition-definition $a |- (
  VERINAB60Pre A
) <-> (
  A e. Word ZZ
) $.

verinab60-program-definition $a |- (
  VERINAB60FindEvenNumbers A
) = (
  VERINAB60Loop A 0 (/)
) $.

${
  $d i A $.

  verinab60-all-even-definition $a |- (
    VERINAB60AllEven A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      ( VERINAB60IsEven ( A ` i ) ) = 1
  ) $.
$}

${
  $d i j k p A B $.

  verinab60-sublist-definition $a |- (
    VERINAB60Sublist A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` A )
        /\
        (
          A. j e. ( 0 ..^ ( # ` A ) )
            (
              ( p ` j ) < ( # ` B )
              /\
              ( A ` j ) = ( B ` ( p ` j ) )
            )
          /\
          A. j e. ( 0 ..^ ( # ` A ) )
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                j < k
                ->
                ( p ` j ) < ( p ` k )
              )
        )
      )
  ) $.
$}

${
  $d i A $.

  verinab60-count-p-definition $a |- (
    VERINAB60CountP A
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( VERINAB60IsEven ( A ` i ) ) = 1
    }
  ) $.
$}

verinab60-postcondition-definition $a |- (
  VERINAB60Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    ( VERINAB60AllEven B )
    /\
    (
      (
        VERINAB60Sublist
          ( VERINAB60ToList B )
          ( VERINAB60ToList A )
      )
      /\
      ( # ` B ) = (
        VERINAB60CountP
          ( VERINAB60ToList A )
      )
    )
  )
) $.

verina-basic-60-find-even-numbers $a |- A. w e. Word ZZ
  (
    ( VERINAB60Pre w )
    ->
    (
      VERINAB60Post
        w
        ( VERINAB60FindEvenNumbers w )
    )
  )
$.
