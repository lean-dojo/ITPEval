$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_89
  (verina__metamath__verina_basic_89), catalog title SetToSeq: the exact
  executable left-to-right integer-list fold removes duplicates while
  retaining first occurrences and satisfies its membership, uniqueness, and
  first-index order correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its natural-number
  length, w ` i is zero-based lookup, ran w is its entry set,
  0 ..^ ( # ` w ) is its complete valid-index set, (/) is the empty word,
  <" x "> is a singleton word, and ++ is word concatenation.

  VERINAB89FoldGraph records every accumulator of the source List.foldl. It
  begins with the empty word and scans the input from left to right. If the
  current integer already belongs to the accumulator range, the accumulator
  is unchanged; otherwise that integer is appended as a singleton. Thus
  VERINAB89SetToSeq selects the unique exact executable result independently
  of the postcondition and admits no additional outputs.

  VERINAB89Count is exactly List.count. VERINAB89IdxOfGraph characterizes
  List.idxOf exactly: it returns the least matching index, or the word length
  when the integer is absent. VERINAB89PairwiseOrder is precisely the source
  List.Pairwise relation on the result: for every earlier/later result pair,
  the result idxOf comparison implies the corresponding input idxOf
  comparison.

  VERINAB89Pre is the source True precondition on typed List Int inputs.
  VERINAB89Post preserves the four source clauses: every result entry belongs
  to the input, every input entry belongs to the result, every result entry
  has count one in the result, and the pairwise idxOf-order condition holds.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB89FoldGraph
  VERINAB89Pre VERINAB89SetToSeq
  VERINAB89Count
  VERINAB89IdxOfGraph VERINAB89IdxOf
  VERINAB89PairwiseOrder VERINAB89Post
$.

verinab89-fold-graph-syntax
  $a wff ( VERINAB89FoldGraph A B ) $.
verinab89-precondition-syntax
  $a wff ( VERINAB89Pre A ) $.
verinab89-program-syntax
  $a class ( VERINAB89SetToSeq A ) $.
verinab89-count-syntax
  $a class ( VERINAB89Count A B ) $.
verinab89-idx-of-graph-syntax
  $a wff ( VERINAB89IdxOfGraph A B C ) $.
verinab89-idx-of-syntax
  $a class ( VERINAB89IdxOf A B ) $.
verinab89-pairwise-order-syntax
  $a wff ( VERINAB89PairwiseOrder A B ) $.
verinab89-postcondition-syntax
  $a wff ( VERINAB89Post A B ) $.

${
  $d k t A B $.

  verinab89-fold-graph-definition $a |- (
    VERINAB89FoldGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` 0 ) = (/)
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              t ` ( k + 1 )
            ) = if (
              ( A ` k ) e. ran ( t ` k ) ,
              ( t ` k ) ,
              ( ( t ` k ) ++ <" ( A ` k ) "> )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

verinab89-precondition-definition $a |- (
  VERINAB89Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d y A $.

  verinab89-program-definition $a |- (
    VERINAB89SetToSeq A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB89FoldGraph A y )
  ) $.
$}

${
  $d i A B $.

  verinab89-count-definition $a |- (
    VERINAB89Count A B
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( A ` i ) = B
    }
  ) $.
$}

${
  $d j A B C $.

  verinab89-idx-of-graph-definition $a |- (
    VERINAB89IdxOfGraph A B C
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
      C <_ ( # ` A )
      /\
      (
        A. j e. ( 0 ..^ C )
          ( A ` j ) =/= B
        /\
        (
          C < ( # ` A )
          ->
          ( A ` C ) = B
        )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verinab89-idx-of-definition $a |- (
    VERINAB89IdxOf A B
  ) = (
    iota_ y e. NN0
      ( VERINAB89IdxOfGraph A B y )
  ) $.
$}

${
  $d i j A B $.

  verinab89-pairwise-order-definition $a |- (
    VERINAB89PairwiseOrder A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    A. i e. ( 0 ..^ ( # ` B ) )
      A. j e. ( 0 ..^ ( # ` B ) )
        (
          i < j
          ->
          (
            (
              VERINAB89IdxOf B ( B ` i )
            ) < (
              VERINAB89IdxOf B ( B ` j )
            )
            ->
            (
              VERINAB89IdxOf A ( B ` i )
            ) < (
              VERINAB89IdxOf A ( B ` j )
            )
          )
        )
  ) $.
$}

${
  $d i A B $.

  verinab89-postcondition-definition $a |- (
    VERINAB89Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` B ) )
        ( B ` i ) e. ran A
      /\
      (
        A. i e. ( 0 ..^ ( # ` A ) )
          ( A ` i ) e. ran B
        /\
        (
          A. i e. ( 0 ..^ ( # ` B ) )
            (
              VERINAB89Count B ( B ` i )
            ) = 1
          /\
          ( VERINAB89PairwiseOrder A B )
        )
      )
    )
  ) $.
$}

verina-basic-89-set-to-seq $a |- A. w e. Word ZZ
  (
    ( VERINAB89Pre w )
    ->
    (
      VERINAB89Post
        w
        ( VERINAB89SetToSeq w )
    )
  )
$.
