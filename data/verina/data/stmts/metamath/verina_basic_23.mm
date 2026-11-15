$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_23
  (verina__metamath__verina_basic_23), catalog title differenceMinMax: the
  exact recursive scan of a nonempty finite integer array returns its running
  maximum minus its running minimum and satisfies the independent fold-based
  minimum-and-maximum correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB23GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB23NatSub is
  Lean's truncated natural subtraction. VERINAB23IntMin and
  VERINAB23IntMax are the source integer conditional minimum and maximum.

  VERINAB23LoopGraph is the exact complete execution trace of the source
  local recursive loop for every array, natural index, and pair of integer
  accumulators. The two trace words begin with minVal and maxVal. For each
  remaining valid array index they read the same get! value and perform the
  source's strict-comparison updates; when the index reaches or exceeds the
  array length, the graph returns final maxVal minus final minVal.
  VERINAB23Loop selects the unique result of this deterministic trace, and
  VERINAB23DifferenceMinMax invokes it at index one with both accumulators
  initialized by a[0]!, exactly as the source executable implementation.

  VERINAB23FoldMinGraph and VERINAB23FoldMaxGraph independently reproduce the
  two source Array.foldl computations from a[0]!, including processing the
  zeroth entry again. Their iota-selected functions therefore denote exactly
  the minimum and maximum expressions occurring in the postcondition.

  VERINAB23Pre preserves the nonempty Array Int precondition. VERINAB23Post
  preserves the source integer equation result + folded minimum = folded
  maximum. The proof-valued precondition argument has no computational effect
  and is represented by the explicit antecedent in the final correctness
  assertion. Every earlier $a is syntax or a faithful definition required by
  this rendering, and this database has no $p declaration.
$)

$c
  VERINAB23GetBang VERINAB23NatSub
  VERINAB23IntMin VERINAB23IntMax
  VERINAB23LoopGraph VERINAB23Loop
  VERINAB23Pre VERINAB23DifferenceMinMax
  VERINAB23FoldMinGraph VERINAB23FoldMin
  VERINAB23FoldMaxGraph VERINAB23FoldMax
  VERINAB23Post
$.

verinab23-get-bang-syntax
  $a class ( VERINAB23GetBang A B ) $.
verinab23-nat-sub-syntax
  $a class ( VERINAB23NatSub A B ) $.
verinab23-int-min-syntax
  $a class ( VERINAB23IntMin A B ) $.
verinab23-int-max-syntax
  $a class ( VERINAB23IntMax A B ) $.
verinab23-loop-graph-syntax
  $a wff ( VERINAB23LoopGraph A B C D E ) $.
verinab23-loop-syntax
  $a class ( VERINAB23Loop A B C D ) $.
verinab23-precondition-syntax
  $a wff ( VERINAB23Pre A ) $.
verinab23-program-syntax
  $a class ( VERINAB23DifferenceMinMax A ) $.
verinab23-fold-min-graph-syntax
  $a wff ( VERINAB23FoldMinGraph A B ) $.
verinab23-fold-min-syntax
  $a class ( VERINAB23FoldMin A ) $.
verinab23-fold-max-graph-syntax
  $a wff ( VERINAB23FoldMaxGraph A B ) $.
verinab23-fold-max-syntax
  $a class ( VERINAB23FoldMax A ) $.
verinab23-postcondition-syntax
  $a wff ( VERINAB23Post A B ) $.

verinab23-get-bang-definition $a |- (
  VERINAB23GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab23-nat-sub-definition $a |- (
  VERINAB23NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab23-int-min-definition $a |- (
  VERINAB23IntMin A B
) = if (
  A < B ,
  A ,
  B
) $.

verinab23-int-max-definition $a |- (
  VERINAB23IntMax A B
) = if (
  A < B ,
  B ,
  A
) $.

${
  $d k m n A B C D E $.

  verinab23-loop-graph-definition $a |- (
    VERINAB23LoopGraph A B C D E
  ) <-> (
    (
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
      E e. ZZ
    )
    /\
    E. m e. Word ZZ
      E. n e. Word ZZ
        (
          (
            (
              ( # ` m ) = (
                ( VERINAB23NatSub ( # ` A ) B ) + 1
              )
              /\
              ( # ` n ) = (
                ( VERINAB23NatSub ( # ` A ) B ) + 1
              )
            )
            /\
            (
              ( m ` 0 ) = C
              /\
              ( n ` 0 ) = D
            )
          )
          /\
          (
            A. k e. (
              0 ..^ ( VERINAB23NatSub ( # ` A ) B )
            )
              (
                (
                  m ` ( k + 1 )
                ) = (
                  VERINAB23IntMin
                    ( VERINAB23GetBang A ( B + k ) )
                    ( m ` k )
                )
                /\
                (
                  n ` ( k + 1 )
                ) = (
                  VERINAB23IntMax
                    ( n ` k )
                    ( VERINAB23GetBang A ( B + k ) )
                )
              )
            /\
            E = (
              (
                n ` ( VERINAB23NatSub ( # ` A ) B )
              )
              -
              (
                m ` ( VERINAB23NatSub ( # ` A ) B )
              )
            )
          )
        )
  ) $.
$}

${
  $d y A B C D $.

  verinab23-loop-definition $a |- (
    VERINAB23Loop A B C D
  ) = (
    iota_ y e. ZZ
      ( VERINAB23LoopGraph A B C D y )
  ) $.
$}

verinab23-precondition-definition $a |- (
  VERINAB23Pre A
) <-> (
  A e. Word ZZ
  /\
  0 < ( # ` A )
) $.

verinab23-program-definition $a |- (
  VERINAB23DifferenceMinMax A
) = (
  VERINAB23Loop
    A
    1
    ( VERINAB23GetBang A 0 )
    ( VERINAB23GetBang A 0 )
) $.

${
  $d k m A B $.

  verinab23-fold-min-graph-definition $a |- (
    VERINAB23FoldMinGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. m e. Word ZZ
      (
        (
          ( # ` m ) = ( ( # ` A ) + 1 )
          /\
          ( m ` 0 ) = ( VERINAB23GetBang A 0 )
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              m ` ( k + 1 )
            ) = (
              VERINAB23IntMin
                ( A ` k )
                ( m ` k )
            )
          /\
          B = ( m ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verinab23-fold-min-definition $a |- (
    VERINAB23FoldMin A
  ) = (
    iota_ y e. ZZ
      ( VERINAB23FoldMinGraph A y )
  ) $.
$}

${
  $d k m A B $.

  verinab23-fold-max-graph-definition $a |- (
    VERINAB23FoldMaxGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. m e. Word ZZ
      (
        (
          ( # ` m ) = ( ( # ` A ) + 1 )
          /\
          ( m ` 0 ) = ( VERINAB23GetBang A 0 )
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              m ` ( k + 1 )
            ) = (
              VERINAB23IntMax
                ( m ` k )
                ( A ` k )
            )
          /\
          B = ( m ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verinab23-fold-max-definition $a |- (
    VERINAB23FoldMax A
  ) = (
    iota_ y e. ZZ
      ( VERINAB23FoldMaxGraph A y )
  ) $.
$}

verinab23-postcondition-definition $a |- (
  VERINAB23Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  (
    B
    +
    ( VERINAB23FoldMin A )
  ) = (
    VERINAB23FoldMax A
  )
) $.

verina-basic-23-difference-min-max $a |- A. a e. Word ZZ
  (
    ( VERINAB23Pre a )
    ->
    (
      VERINAB23Post
        a
        ( VERINAB23DifferenceMinMax a )
    )
  )
$.
