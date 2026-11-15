$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_34
  (verina__metamath__verina_basic_34), catalog title findEvenNumbers: the
  exact executable left-to-right integer-array fold retains precisely the
  even entries in their original order and satisfies the complete
  multiplicity, membership, and idxOf-order correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer arrays and lists. For a word w, # ` w is its
  natural-number length, w ` i is zero-based lookup, ran w is its entry set,
  0 ..^ ( # ` w ) is its complete valid-index set, (/) is the empty word,
  <" x "> is a singleton word, and ++ is word concatenation.

  VERINAB34IsEven is the source Boolean helper isEven: it is one exactly when
  Lean's integer Euclidean remainder modulo two is zero, and zero otherwise.
  VERINAB34ToList is the source Array.toList conversion, extensionally the
  identity on the finite-word representation.

  VERINAB34FoldGraph records every accumulator of the source Array.foldl.
  It starts with the empty word and scans every input entry from left to
  right. An even entry is appended to the accumulator exactly as Array.push
  does; an odd entry leaves the accumulator unchanged. VERINAB34FindEvenNumbers
  selects the unique final accumulator, so the executable result is fixed
  independently of the postcondition and admits no additional outputs.

  VERINAB34Count is List.count. VERINAB34IdxOfGraph characterizes List.idxOf
  exactly: it returns the least matching index, or the word length when the
  integer is absent. VERINAB34Post preserves all three source clauses:
  every result entry is even, belongs to the input, and has the same full
  multiplicity there; every even input entry belongs to the result; and the
  nested source Array.all implication compares the same first-occurrence
  idxOf values for every ordered pair of input entries.

  VERINAB34Pre is the source True precondition on typed Array Int inputs.
  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB34IsEven VERINAB34ToList
  VERINAB34FoldGraph
  VERINAB34Pre VERINAB34FindEvenNumbers
  VERINAB34Count
  VERINAB34IdxOfGraph VERINAB34IdxOf
  VERINAB34Post
$.

verinab34-is-even-syntax
  $a class ( VERINAB34IsEven A ) $.
verinab34-to-list-syntax
  $a class ( VERINAB34ToList A ) $.
verinab34-fold-graph-syntax
  $a wff ( VERINAB34FoldGraph A B ) $.
verinab34-precondition-syntax
  $a wff ( VERINAB34Pre A ) $.
verinab34-program-syntax
  $a class ( VERINAB34FindEvenNumbers A ) $.
verinab34-count-syntax
  $a class ( VERINAB34Count A B ) $.
verinab34-idx-of-graph-syntax
  $a wff ( VERINAB34IdxOfGraph A B C ) $.
verinab34-idx-of-syntax
  $a class ( VERINAB34IdxOf A B ) $.
verinab34-postcondition-syntax
  $a wff ( VERINAB34Post A B ) $.

verinab34-is-even-definition $a |- (
  VERINAB34IsEven A
) = if (
  ( A mod 2 ) = 0 ,
  1 ,
  0
) $.

verinab34-to-list-definition $a |- (
  VERINAB34ToList A
) = A $.

${
  $d k t A B $.

  verinab34-fold-graph-definition $a |- (
    VERINAB34FoldGraph A B
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
              ( VERINAB34IsEven ( A ` k ) ) = 1 ,
              ( ( t ` k ) ++ <" ( A ` k ) "> ) ,
              ( t ` k )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

verinab34-precondition-definition $a |- (
  VERINAB34Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d y A $.

  verinab34-program-definition $a |- (
    VERINAB34FindEvenNumbers A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB34FoldGraph A y )
  ) $.
$}

${
  $d i A B $.

  verinab34-count-definition $a |- (
    VERINAB34Count A B
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

  verinab34-idx-of-graph-definition $a |- (
    VERINAB34IdxOfGraph A B C
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

  verinab34-idx-of-definition $a |- (
    VERINAB34IdxOf A B
  ) = (
    iota_ y e. NN0
      ( VERINAB34IdxOfGraph A B y )
  ) $.
$}

${
  $d i j A B $.

  verinab34-postcondition-definition $a |- (
    VERINAB34Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` B ) )
        (
          (
            ( VERINAB34IsEven ( B ` i ) ) = 1
            /\
            ( B ` i ) e. ran ( VERINAB34ToList A )
          )
          /\
          (
            VERINAB34Count
              ( VERINAB34ToList B )
              ( B ` i )
          ) = (
            VERINAB34Count
              ( VERINAB34ToList A )
              ( B ` i )
          )
        )
      /\
      (
        A. i e. ( 0 ..^ ( # ` A ) )
          (
            ( VERINAB34IsEven ( A ` i ) ) = 1
            ->
            ( A ` i ) e. ran ( VERINAB34ToList B )
          )
        /\
        A. i e. ( 0 ..^ ( # ` A ) )
          A. j e. ( 0 ..^ ( # ` A ) )
            (
              ( VERINAB34IsEven ( A ` i ) ) = 1
              ->
              (
                ( VERINAB34IsEven ( A ` j ) ) = 1
                ->
                (
                  (
                    VERINAB34IdxOf
                      ( VERINAB34ToList A )
                      ( A ` i )
                  ) <_ (
                    VERINAB34IdxOf
                      ( VERINAB34ToList A )
                      ( A ` j )
                  )
                  ->
                  (
                    VERINAB34IdxOf
                      ( VERINAB34ToList B )
                      ( A ` i )
                  ) <_ (
                    VERINAB34IdxOf
                      ( VERINAB34ToList B )
                      ( A ` j )
                  )
                )
              )
            )
      )
    )
  ) $.
$}

verina-basic-34-find-even-numbers $a |- A. w e. Word ZZ
  (
    ( VERINAB34Pre w )
    ->
    (
      VERINAB34Post
        w
        ( VERINAB34FindEvenNumbers w )
    )
  )
$.
