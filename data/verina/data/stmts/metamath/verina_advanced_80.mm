$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_80 (verina__metamath__verina_advanced_80), catalog title
  twoSum: the exact fuel-bounded nested array search returns the two sorted
  natural indices of the unique pair of integer entries whose sum is the
  target, under its complete precondition and postcondition contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ and Word NN0 are exactly the types of arbitrary finite integer and
  natural-number arrays. For a word w, # ` w is its natural-number length,
  w ` k is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA80GetBang reproduces Lean Array.get! with numeric default zero.
  VERINA80PairWord constructs the two-entry natural word #[i, j].
  VERINA80MatchingPairs contains exactly the ordered pairs (i,j) with j < i
  whose array entries sum to the target. Consequently VERINA80Pre preserves
  the source size bound, its explicit List.any existence test, and the
  length-one flatMap/filter uniqueness test.

  VERINA80FindIndicesGraph is an exact operational graph for the local
  findIndices recursion at arbitrary natural i, j, and fuel. Its trace has
  fuel + 1 states. Each of the first fuel states follows the source branch:
  an out-of-range i freezes the terminal state; an out-of-range j advances i
  and resets j to the new i + 1; a matching in-range pair freezes the
  successful state; otherwise j is incremented. The result is the matching
  pair exactly when such a state was inspected before fuel exhaustion, and
  is the empty word otherwise. Thus the graph permits no extra outputs.
  VERINA80FindIndices selects its unique result, and VERINA80TwoSum invokes
  it at i = 0, j = 1, and fuel equal to the square of the array length.

  VERINA80Post preserves the result length, both bounds, strict index order,
  and zero-default indexed integer sum. The proof-valued precondition
  arguments to twoSum and the postcondition are computationally and
  propositionally unused, so the explicit antecedent of the final
  correctness assertion represents them. Every earlier $a is syntax or a
  faithful definition required by this rendering, and this database has no
  $p declaration.
$)

$c
  VERINA80GetBang
  VERINA80PairWordGraph VERINA80PairWord
  VERINA80MatchingPairs
  VERINA80FindIndicesGraph VERINA80FindIndices VERINA80TwoSum
  VERINA80Pre VERINA80Post
$.

verina80-get-bang-syntax
  $a class ( VERINA80GetBang A B ) $.
verina80-pair-word-graph-syntax
  $a wff ( VERINA80PairWordGraph A B C ) $.
verina80-pair-word-syntax
  $a class ( VERINA80PairWord A B ) $.
verina80-matching-pairs-syntax
  $a class ( VERINA80MatchingPairs A B ) $.
verina80-find-indices-graph-syntax
  $a wff ( VERINA80FindIndicesGraph A B C D E F ) $.
verina80-find-indices-syntax
  $a class ( VERINA80FindIndices A B C D E ) $.
verina80-two-sum-syntax
  $a class ( VERINA80TwoSum A B ) $.
verina80-precondition-syntax
  $a wff ( VERINA80Pre A B ) $.
verina80-postcondition-syntax
  $a wff ( VERINA80Post A B C ) $.

verina80-get-bang-definition $a |- (
  VERINA80GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d A B C $.

  verina80-pair-word-graph-definition $a |- (
    VERINA80PairWordGraph A B C
  ) <-> (
    (
      (
        A e. NN0
        /\
        B e. NN0
      )
      /\
      C e. Word NN0
    )
    /\
    (
      ( # ` C ) = 2
      /\
      (
        ( C ` 0 ) = A
        /\
        ( C ` 1 ) = B
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina80-pair-word-definition $a |- (
    VERINA80PairWord A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA80PairWordGraph A B y )
  ) $.
$}

${
  $d p A B $.

  verina80-matching-pairs-definition $a |- (
    VERINA80MatchingPairs A B
  ) = {
    p e. (
      ( 0 ..^ ( # ` A ) )
      X.
      ( 0 ..^ ( # ` A ) )
    )
    |
    (
      ( 2nd ` p ) < ( 1st ` p )
      /\
      (
        ( A ` ( 1st ` p ) )
        +
        ( A ` ( 2nd ` p ) )
      ) = B
    )
  } $.
$}

${
  $d k t A B C D E F $.

  verina80-find-indices-graph-definition $a |- (
    VERINA80FindIndicesGraph A B C D E F
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
          (
            C e. NN0
            /\
            D e. NN0
          )
        )
        /\
        E e. NN0
      )
      /\
      F e. Word NN0
    )
    /\
    E. t e. Word ( NN0 X. NN0 )
      (
        (
          ( # ` t ) = ( E + 1 )
          /\
          ( t ` 0 ) = <. C , D >.
        )
        /\
        (
          A. k e. ( 0 ..^ E )
            (
              t ` ( k + 1 )
            ) = if (
              (
                # ` A
              ) <_ (
                1st ` ( t ` k )
              ) ,
              ( t ` k ) ,
              if (
                (
                  # ` A
                ) <_ (
                  2nd ` ( t ` k )
                ) ,
                <.
                  ( ( 1st ` ( t ` k ) ) + 1 ) ,
                  ( ( 1st ` ( t ` k ) ) + 2 )
                >. ,
                if (
                  (
                    (
                      A ` ( 1st ` ( t ` k ) )
                    ) + (
                      A ` ( 2nd ` ( t ` k ) )
                    )
                  ) = B ,
                  ( t ` k ) ,
                  <.
                    ( 1st ` ( t ` k ) ) ,
                    ( ( 2nd ` ( t ` k ) ) + 1 )
                  >.
                )
              )
            )
          /\
          (
            E. k e. ( 0 ..^ E )
              (
                (
                  (
                    1st ` ( t ` k )
                  ) < (
                    # ` A
                  )
                  /\
                  (
                    2nd ` ( t ` k )
                  ) < (
                    # ` A
                  )
                )
                /\
                (
                  (
                    (
                      A ` ( 1st ` ( t ` k ) )
                    ) + (
                      A ` ( 2nd ` ( t ` k ) )
                    )
                  ) = B
                  /\
                  F = (
                    VERINA80PairWord
                      ( 1st ` ( t ` k ) )
                      ( 2nd ` ( t ` k ) )
                  )
                )
              )
            \/
            (
              -.
              E. k e. ( 0 ..^ E )
                (
                  (
                    (
                      1st ` ( t ` k )
                    ) < (
                      # ` A
                    )
                    /\
                    (
                      2nd ` ( t ` k )
                    ) < (
                      # ` A
                    )
                  )
                  /\
                  (
                    (
                      A ` ( 1st ` ( t ` k ) )
                    ) + (
                      A ` ( 2nd ` ( t ` k ) )
                    )
                  ) = B
                )
              /\
              F = (/)
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verina80-find-indices-definition $a |- (
    VERINA80FindIndices A B C D E
  ) = (
    iota_ y e. Word NN0
      (
        VERINA80FindIndicesGraph
          A B C D E y
      )
  ) $.
$}

verina80-two-sum-definition $a |- (
  VERINA80TwoSum A B
) = (
  VERINA80FindIndices
    A
    B
    0
    1
    ( ( # ` A ) x. ( # ` A ) )
) $.

${
  $d i j A B $.

  verina80-precondition-definition $a |- (
    VERINA80Pre A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      2 <_ ( # ` A )
      /\
      (
        E. i e. ( 0 ..^ ( # ` A ) )
          E. j e. ( 0 ..^ i )
            (
              ( A ` i ) + ( A ` j )
            ) = B
        /\
        (
          # ` ( VERINA80MatchingPairs A B )
        ) = 1
      )
    )
  ) $.
$}

verina80-postcondition-definition $a |- (
  VERINA80Post A B C
) <-> (
  (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    C e. Word NN0
  )
  /\
  (
    ( # ` C ) = 2
    /\
    (
      (
        VERINA80GetBang C 0
      ) < (
        # ` A
      )
      /\
      (
        (
          VERINA80GetBang C 1
        ) < (
          # ` A
        )
        /\
        (
          (
            VERINA80GetBang C 0
          ) < (
            VERINA80GetBang C 1
          )
          /\
          (
            (
              VERINA80GetBang
                A
                ( VERINA80GetBang C 0 )
            ) + (
              VERINA80GetBang
                A
                ( VERINA80GetBang C 1 )
            )
          ) = B
        )
      )
    )
  )
) $.

${
  $d w z $.

  verina-advanced-80-two-sum $a |- A. w e. Word ZZ
    A. z e. ZZ
      (
        ( VERINA80Pre w z )
        ->
        (
          VERINA80Post
            w
            z
            ( VERINA80TwoSum w z )
        )
      )
  $.
$}
