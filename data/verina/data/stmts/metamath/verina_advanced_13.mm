$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_13, catalog title hasChordIntersection: an executable
  normalization, insertion sort, and stack scan decides whether a finite
  family of chords has an alternating-endpoint intersection, together with
  its precondition and Boolean correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain. Word NN0 is exactly the
  type of arbitrary finite natural-number lists, and Word ( Word NN0 ) is
  the type of arbitrary finite lists of such lists. Function application to
  an index outside a word's domain is the empty set, which is ordinal zero,
  matching Lean's Nat-valued List.get! default.

  VERINA13Normalize is the source map that orders the two endpoints of every
  chord. VERINA13InsertGraph and VERINA13SortGraph give the exact recursive
  insertion and insertion-sort computations; the sort trace inserts the
  input chords from right to left, exactly as the source recursion does.

  VERINA13DropGraph is List.dropWhile for the stack predicate c[1] < a.
  VERINA13Hit is precisely the successful top-of-stack test, and
  VERINA13NoHitStep is precisely one recursive stack update. The two branches
  of VERINA13CheckGraph describe, respectively, the first successful scan
  step and a complete unsuccessful scan. Hence VERINA13Program is the exact
  executable hasChordIntersection computation, not an unconstrained output
  relation and not an existential choice satisfying the postcondition.

  VERINA13IntersectionBool is the local hasIntersection Boolean helper, and
  VERINA13CheckAllPairs is the exact local recursive pair scan (although that
  local helper is unused by the source postcondition body). VERINA13Pre
  reproduces the lower bound, chord count, endpoint bounds, and global
  duplicate-freedom precondition. VERINA13Post reproduces both implications
  of the source postcondition, including List.Pairwise and the nested any
  searches. The proof-valued precondition arguments are computationally
  unused and are omitted from the target functions. The final $a declaration
  is the source correctness proposition; every earlier $a is syntax or a
  faithful definition, and this database has no $p declaration.
$)

$c
  VERINA13NormalizeGraph VERINA13Normalize
  VERINA13InsertGraph VERINA13Insert
  VERINA13SortGraph VERINA13Sort
  VERINA13DropGraph VERINA13Drop
  VERINA13Hit VERINA13NoHitStep
  VERINA13CheckGraph VERINA13Check
  VERINA13Program
  VERINA13IntersectionBool
  VERINA13CheckAllPairsGraph VERINA13CheckAllPairs
  VERINA13PairwiseClear VERINA13AnyIntersection
  VERINA13Pre VERINA13Post
$.

verina13-normalize-graph-syntax
  $a wff ( VERINA13NormalizeGraph A B ) $.
verina13-normalize-syntax
  $a class ( VERINA13Normalize A ) $.
verina13-insert-graph-syntax
  $a wff ( VERINA13InsertGraph A B C ) $.
verina13-insert-syntax
  $a class ( VERINA13Insert A B ) $.
verina13-sort-graph-syntax
  $a wff ( VERINA13SortGraph A B ) $.
verina13-sort-syntax
  $a class ( VERINA13Sort A ) $.
verina13-drop-graph-syntax
  $a wff ( VERINA13DropGraph A B C ) $.
verina13-drop-syntax
  $a class ( VERINA13Drop A B ) $.
verina13-hit-syntax
  $a wff ( VERINA13Hit A B ) $.
verina13-no-hit-step-syntax
  $a wff ( VERINA13NoHitStep A B C ) $.
verina13-check-graph-syntax
  $a wff ( VERINA13CheckGraph A B ) $.
verina13-check-syntax
  $a class ( VERINA13Check A ) $.
verina13-program-syntax
  $a class ( VERINA13Program A B ) $.
verina13-intersection-bool-syntax
  $a class ( VERINA13IntersectionBool A B ) $.
verina13-check-all-pairs-graph-syntax
  $a wff ( VERINA13CheckAllPairsGraph A B ) $.
verina13-check-all-pairs-syntax
  $a class ( VERINA13CheckAllPairs A ) $.
verina13-pairwise-clear-syntax
  $a wff ( VERINA13PairwiseClear A ) $.
verina13-any-intersection-syntax
  $a wff ( VERINA13AnyIntersection A ) $.
verina13-precondition-syntax
  $a wff ( VERINA13Pre A B ) $.
verina13-postcondition-syntax
  $a wff ( VERINA13Post A B C ) $.

${
  $d k A B $.

  verina13-normalize-graph-definition $a |- (
    VERINA13NormalizeGraph A B
  ) <-> (
    (
      A e. Word ( Word NN0 )
      /\
      B e. Word ( Word NN0 )
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        (
          ( # ` ( B ` k ) ) = 2
          /\
          (
            (
              ( B ` k ) ` 0
            ) = if (
              ( ( A ` k ) ` 1 ) < ( ( A ` k ) ` 0 ) ,
              ( A ` k ) ` 1 ,
              ( A ` k ) ` 0
            )
            /\
            (
              ( B ` k ) ` 1
            ) = if (
              ( ( A ` k ) ` 1 ) < ( ( A ` k ) ` 0 ) ,
              ( A ` k ) ` 0 ,
              ( A ` k ) ` 1
            )
          )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina13-normalize-definition $a |- (
    VERINA13Normalize A
  ) = (
    iota_ y e. Word ( Word NN0 )
      ( VERINA13NormalizeGraph A y )
  ) $.
$}

${
  $d j p A B C $.

  verina13-insert-graph-definition $a |- (
    VERINA13InsertGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. Word ( Word NN0 )
      )
      /\
      C e. Word ( Word NN0 )
    )
    /\
    E. p e. NN0
      (
        p <_ ( # ` B )
        /\
        (
          (
            A. j e. ( 0 ..^ p )
              -. ( ( A ` 0 ) < ( ( B ` j ) ` 0 ) )
            /\
            (
              p < ( # ` B )
              ->
              ( A ` 0 ) < ( ( B ` p ) ` 0 )
            )
          )
          /\
          (
            ( # ` C ) = ( ( # ` B ) + 1 )
            /\
            (
              ( C ` p ) = A
              /\
              (
                A. j e. ( 0 ..^ p )
                  ( C ` j ) = ( B ` j )
                /\
                A. j e. ( p ..^ ( # ` B ) )
                  ( C ` ( j + 1 ) ) = ( B ` j )
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina13-insert-definition $a |- (
    VERINA13Insert A B
  ) = (
    iota_ y e. Word ( Word NN0 )
      ( VERINA13InsertGraph A B y )
  ) $.
$}

${
  $d k t A B $.

  verina13-sort-graph-definition $a |- (
    VERINA13SortGraph A B
  ) <-> (
    (
      A e. Word ( Word NN0 )
      /\
      B e. Word ( Word NN0 )
    )
    /\
    E. t e. Word ( Word ( Word NN0 ) )
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
              VERINA13InsertGraph
                ( A ` ( ( ( # ` A ) - 1 ) - k ) )
                ( t ` k )
                ( t ` ( k + 1 ) )
            )
          /\
          B = ( t ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina13-sort-definition $a |- (
    VERINA13Sort A
  ) = (
    iota_ y e. Word ( Word NN0 )
      ( VERINA13SortGraph A y )
  ) $.
$}

${
  $d j p A B C $.

  verina13-drop-graph-definition $a |- (
    VERINA13DropGraph A B C
  ) <-> (
    (
      (
        A e. Word ( Word NN0 )
        /\
        B e. NN0
      )
      /\
      C e. Word ( Word NN0 )
    )
    /\
    E. p e. NN0
      (
        p <_ ( # ` A )
        /\
        (
          (
            A. j e. ( 0 ..^ p )
              ( ( A ` j ) ` 1 ) < B
            /\
            (
              p < ( # ` A )
              ->
              -. ( ( ( A ` p ) ` 1 ) < B )
            )
          )
          /\
          (
            ( # ` C ) = ( ( # ` A ) - p )
            /\
            A. j e. ( 0 ..^ ( # ` C ) )
              ( C ` j ) = ( A ` ( j + p ) )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina13-drop-definition $a |- (
    VERINA13Drop A B
  ) = (
    iota_ y e. Word ( Word NN0 )
      ( VERINA13DropGraph A B y )
  ) $.
$}

verina13-hit-definition $a |- (
  VERINA13Hit A B
) <-> (
  (
    A e. Word ( Word NN0 )
    /\
    B e. Word NN0
  )
  /\
  (
    0 < ( # ` ( VERINA13Drop A ( B ` 0 ) ) )
    /\
    (
      ( B ` 0 )
        < ( ( ( VERINA13Drop A ( B ` 0 ) ) ` 0 ) ` 1 )
      /\
      ( ( ( VERINA13Drop A ( B ` 0 ) ) ` 0 ) ` 1 )
        < ( B ` 1 )
    )
  )
) $.

${
  $d j A B C $.

  verina13-no-hit-step-definition $a |- (
    VERINA13NoHitStep A B C
  ) <-> (
    (
      (
        A e. Word ( Word NN0 )
        /\
        B e. Word NN0
      )
      /\
      C e. Word ( Word NN0 )
    )
    /\
    (
      -. ( VERINA13Hit A B )
      /\
      (
        ( # ` C ) =
          ( ( # ` ( VERINA13Drop A ( B ` 0 ) ) ) + 1 )
        /\
        (
          ( C ` 0 ) = B
          /\
          A. j e.
            ( 0 ..^ ( # ` ( VERINA13Drop A ( B ` 0 ) ) ) )
            (
              C ` ( j + 1 )
            ) = (
              ( VERINA13Drop A ( B ` 0 ) ) ` j
            )
        )
      )
    )
  ) $.
$}

${
  $d j k t A B $.

  verina13-check-graph-definition $a |- (
    VERINA13CheckGraph A B
  ) <-> (
    (
      A e. Word ( Word NN0 )
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      (
        B = 1
        /\
        E. k e. ( 0 ..^ ( # ` A ) )
          E. t e. Word ( Word ( Word NN0 ) )
            (
              (
                ( # ` t ) = ( k + 1 )
                /\
                ( t ` 0 ) = (/)
              )
              /\
              (
                A. j e. ( 0 ..^ k )
                  (
                    VERINA13NoHitStep
                      ( t ` j )
                      ( A ` j )
                      ( t ` ( j + 1 ) )
                  )
                /\
                ( VERINA13Hit ( t ` k ) ( A ` k ) )
              )
            )
      )
      \/
      (
        B = 0
        /\
        E. t e. Word ( Word ( Word NN0 ) )
          (
            (
              ( # ` t ) = ( ( # ` A ) + 1 )
              /\
              ( t ` 0 ) = (/)
            )
            /\
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                VERINA13NoHitStep
                  ( t ` k )
                  ( A ` k )
                  ( t ` ( k + 1 ) )
              )
          )
      )
    )
  ) $.
$}

${
  $d y A $.

  verina13-check-definition $a |- (
    VERINA13Check A
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA13CheckGraph A y )
  ) $.
$}

verina13-program-definition $a |- (
  VERINA13Program A B
) = (
  VERINA13Check
    ( VERINA13Sort ( VERINA13Normalize B ) )
) $.

verina13-intersection-bool-definition $a |- (
  VERINA13IntersectionBool A B
) = if (
  (
    (
      (
        ( A ` 0 ) < ( B ` 0 )
        /\
        ( B ` 0 ) < ( A ` 1 )
      )
      /\
      ( A ` 1 ) < ( B ` 1 )
    )
    \/
    (
      (
        ( B ` 0 ) < ( A ` 0 )
        /\
        ( A ` 0 ) < ( B ` 1 )
      )
      /\
      ( B ` 1 ) < ( A ` 1 )
    )
  ) ,
  1 ,
  0
) $.

${
  $d i j A B $.

  verina13-check-all-pairs-graph-definition $a |- (
    VERINA13CheckAllPairsGraph A B
  ) <-> (
    (
      A e. Word ( Word NN0 )
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      (
        B = 1
        /\
        E. i e. ( 0 ..^ ( # ` A ) )
          E. j e. ( 0 ..^ ( # ` A ) )
            (
              i < j
              /\
              ( VERINA13IntersectionBool
                  ( A ` i ) ( A ` j ) ) = 1
            )
      )
      \/
      (
        B = 0
        /\
        -.
        E. i e. ( 0 ..^ ( # ` A ) )
          E. j e. ( 0 ..^ ( # ` A ) )
            (
              i < j
              /\
              ( VERINA13IntersectionBool
                  ( A ` i ) ( A ` j ) ) = 1
            )
      )
    )
  ) $.
$}

${
  $d y A $.

  verina13-check-all-pairs-definition $a |- (
    VERINA13CheckAllPairs A
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINA13CheckAllPairsGraph A y )
  ) $.
$}

${
  $d i j A $.

  verina13-pairwise-clear-definition $a |- (
    VERINA13PairwiseClear A
  ) <-> (
    (
      A e. Word ( Word NN0 )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( VERINA13IntersectionBool
                ( A ` i ) ( A ` j ) ) = 0
          )
    )
  ) $.
$}

${
  $d i j A $.

  verina13-any-intersection-definition $a |- (
    VERINA13AnyIntersection A
  ) <-> (
    (
      A e. Word ( Word NN0 )
      /\
      E. i e. ( 0 ..^ ( # ` A ) )
        E. j e. ( 0 ..^ ( # ` A ) )
          ( VERINA13IntersectionBool
              ( A ` i ) ( A ` j ) ) = 1
    )
  ) $.
$}

${
  $d i j p q A B $.

  verina13-precondition-definition $a |- (
    VERINA13Pre A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. Word ( Word NN0 )
    )
    /\
    (
      2 <_ A
      /\
      (
        ( # ` B ) = A
        /\
        (
          A. i e. ( 0 ..^ ( # ` B ) )
            (
              ( # ` ( B ` i ) ) = 2
              /\
              (
                (
                  1 <_ ( ( B ` i ) ` 0 )
                  /\
                  ( ( B ` i ) ` 0 ) <_ ( 2 x. A )
                )
                /\
                (
                  1 <_ ( ( B ` i ) ` 1 )
                  /\
                  ( ( B ` i ) ` 1 ) <_ ( 2 x. A )
                )
              )
            )
          /\
          A. i e. ( 0 ..^ ( # ` B ) )
            A. p e. ( 0 ..^ ( # ` ( B ` i ) ) )
              A. j e. ( 0 ..^ ( # ` B ) )
                A. q e. ( 0 ..^ ( # ` ( B ` j ) ) )
                  (
                    (
                      i =/= j
                      \/
                      p =/= q
                    )
                    ->
                    ( ( B ` i ) ` p ) =/= ( ( B ` j ) ` q )
                  )
        )
      )
    )
  ) $.
$}

verina13-postcondition-definition $a |- (
  VERINA13Post A B C
) <-> (
  (
    (
      A e. NN0
      /\
      B e. Word ( Word NN0 )
    )
    /\
    C e. { 0 , 1 }
  )
  /\
  (
    (
      ( VERINA13PairwiseClear ( VERINA13Normalize B ) )
      ->
      C = 0
    )
    /\
    (
      ( VERINA13AnyIntersection ( VERINA13Normalize B ) )
      ->
      C = 1
    )
  )
) $.

verina-advanced-13-has-chord-intersection $a |- A. n e. NN0
  A. w e. Word ( Word NN0 )
    (
      ( VERINA13Pre n w )
      ->
      (
        VERINA13Post
          n
          w
          ( VERINA13Program n w )
      )
    )
$.
