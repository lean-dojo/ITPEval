$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_32 (verina__metamath__verina_advanced_32), catalog title
  longestIncreasingSubsequence: the exact dynamic-programming list program
  computes the natural-number length of a longest strictly increasing
  subsequence of an arbitrary finite integer list. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA32FindLengthEndingAtCurrGraph is the exact accumulator trace of the
  local findLengthEndingAtCurr call made while processing input position k.
  It scans the already-built prefixes numbers[0..k) and lengths[0..k), starts
  best at zero, and replaces best by Nat.max best lengths[j] exactly when
  numbers[j] < numbers[k]. VERINA32FindLengthEndingAtCurr selects its unique
  result.

  VERINA32BuildTablesGraph records the lengths list produced by buildTables.
  For nonempty input its first entry is one, and each later entry is one plus
  VERINA32FindLengthEndingAtCurr on the preceding entries. At iteration k,
  the source prevNums and lengths arguments are exactly the prefixes through
  k - 1, while restNums begins at numbers[k]. Appending the current number
  and length therefore gives precisely the next graph entry. The source idx
  argument starts at one and is incremented once per iteration, but is never
  inspected and cannot affect the returned value.

  VERINA32FindMaxLengthGraph follows the source's right-recursive
  findMaxLength helper from its empty-list result zero. VERINA32BuildTables
  selects the unique result of the table graph, and
  VERINA32LongestIncreasingSubsequence preserves the source's explicit empty
  and singleton branches before using that buildTables result.

  VERINA32BitSet and VERINA32PostMaskWordGraph reproduce the postcondition's
  fold
    acc ++ acc.map (fun sub => x :: sub)
  from [[]], followed by List.reverse on every result: mask bit k selects
  input position k, numeric mask order is the fold's append order, and the
  selected positions occur in increasing input order after the reverse.
  VERINA32PostStrictlyIncreasing is exactly List.Pairwise (<).
  VERINA32PostIncreasingLensGraph is the stable filter by that predicate
  followed by the natural-number length map. VERINA32Post then reproduces
  List.contains for the returned length and List.all asserting that every
  retained length is at most it.

  VERINA32Pre is the source True precondition together with the List Int
  input type. The proof-valued precondition argument is computationally and
  propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database has
  no $p declaration.
$)

$c
  VERINA32NatMax
  VERINA32FindLengthEndingAtCurrGraph
  VERINA32FindLengthEndingAtCurr
  VERINA32FindMaxLengthGraph VERINA32FindMaxLength
  VERINA32BuildTablesGraph VERINA32BuildTables
  VERINA32LongestIncreasingSubsequence VERINA32Pre
  VERINA32BitSet
  VERINA32PostMaskWordGraph
  VERINA32PostSubsequencesGraph VERINA32PostSubsequences
  VERINA32PostStrictlyIncreasing
  VERINA32PostIncreasingLensGraph VERINA32PostIncreasingLens
  VERINA32Post
$.

verina32-nat-max-syntax
  $a class ( VERINA32NatMax A B ) $.
verina32-find-length-ending-at-curr-graph-syntax
  $a wff ( VERINA32FindLengthEndingAtCurrGraph A B C D ) $.
verina32-find-length-ending-at-curr-syntax
  $a class ( VERINA32FindLengthEndingAtCurr A B C ) $.
verina32-find-max-length-graph-syntax
  $a wff ( VERINA32FindMaxLengthGraph A B ) $.
verina32-find-max-length-syntax
  $a class ( VERINA32FindMaxLength A ) $.
verina32-build-tables-graph-syntax
  $a wff ( VERINA32BuildTablesGraph A B C ) $.
verina32-build-tables-syntax
  $a class ( VERINA32BuildTables A ) $.
verina32-longest-increasing-subsequence-syntax
  $a class ( VERINA32LongestIncreasingSubsequence A ) $.
verina32-precondition-syntax
  $a wff ( VERINA32Pre A ) $.
verina32-bit-set-syntax
  $a wff ( VERINA32BitSet A B ) $.
verina32-post-mask-word-graph-syntax
  $a wff ( VERINA32PostMaskWordGraph A B C ) $.
verina32-post-subsequences-graph-syntax
  $a wff ( VERINA32PostSubsequencesGraph A B ) $.
verina32-post-subsequences-syntax
  $a class ( VERINA32PostSubsequences A ) $.
verina32-post-strictly-increasing-syntax
  $a wff ( VERINA32PostStrictlyIncreasing A ) $.
verina32-post-increasing-lens-graph-syntax
  $a wff ( VERINA32PostIncreasingLensGraph A B ) $.
verina32-post-increasing-lens-syntax
  $a class ( VERINA32PostIncreasingLens A ) $.
verina32-postcondition-syntax
  $a wff ( VERINA32Post A B ) $.

verina32-nat-max-definition $a |- (
  VERINA32NatMax A B
) = if (
  A < B ,
  B ,
  A
) $.

${
  $d j s A B C D $.

  verina32-find-length-ending-at-curr-graph-definition $a |- (
    VERINA32FindLengthEndingAtCurrGraph A B C D
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word NN0
      )
      /\
      (
        C e. NN0
        /\
        D e. NN0
      )
    )
    /\
    (
      (
        C < ( # ` A )
        /\
        C < ( # ` B )
      )
      /\
      E. s e. Word NN0
        (
          (
            ( # ` s ) = ( C + 1 )
            /\
            ( s ` 0 ) = 0
          )
          /\
          (
            A. j e. ( 0 ..^ C )
              (
                s ` ( j + 1 )
              ) = if (
                ( A ` j ) < ( A ` C ) ,
                VERINA32NatMax
                  ( s ` j )
                  ( B ` j ) ,
                ( s ` j )
              )
            /\
            D = ( s ` C )
          )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verina32-find-length-ending-at-curr-definition $a |- (
    VERINA32FindLengthEndingAtCurr A B C
  ) = (
    iota_ y e. NN0
      ( VERINA32FindLengthEndingAtCurrGraph A B C y )
  ) $.
$}

${
  $d k s A B $.

  verina32-find-max-length-graph-definition $a |- (
    VERINA32FindMaxLengthGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. NN0
    )
    /\
    E. s e. Word NN0
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` ( # ` A ) ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` k
            ) = (
              VERINA32NatMax
                ( A ` k )
                ( s ` ( k + 1 ) )
            )
          /\
          B = ( s ` 0 )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina32-find-max-length-definition $a |- (
    VERINA32FindMaxLength A
  ) = (
    iota_ y e. NN0
      ( VERINA32FindMaxLengthGraph A y )
  ) $.
$}

${
  $d k A B C $.

  verina32-build-tables-graph-definition $a |- (
    VERINA32BuildTablesGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word NN0
      )
      /\
      C e. NN0
    )
    /\
    (
      (
        0 < ( # ` A )
        /\
        ( # ` B ) = ( # ` A )
      )
      /\
      (
        ( B ` 0 ) = 1
        /\
        A. k e. ( 1 ..^ ( # ` A ) )
          (
            B ` k
          ) = (
            (
              VERINA32FindLengthEndingAtCurr
                A B k
            ) + 1
          )
        /\
        C = ( VERINA32FindMaxLength B )
      )
    )
  ) $.
$}

${
  $d l y A $.

  verina32-build-tables-definition $a |- (
    VERINA32BuildTables A
  ) = (
    iota_ y e. NN0
      E. l e. Word NN0
        ( VERINA32BuildTablesGraph A l y )
  ) $.
$}

verina32-longest-increasing-subsequence-definition $a |- (
  VERINA32LongestIncreasingSubsequence A
) = if (
  ( # ` A ) = 0 ,
  0 ,
  if (
    ( # ` A ) = 1 ,
    1 ,
    ( VERINA32BuildTables A )
  )
) $.

verina32-precondition-definition $a |- (
  VERINA32Pre A
) <-> (
  A e. Word ZZ
) $.

verina32-bit-set-definition $a |- (
  VERINA32BitSet A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    ( |_ ` ( A / ( 2 ^ B ) ) ) mod 2
  ) = 1
) $.

${
  $d i j k p A B C $.

  verina32-post-mask-word-graph-definition $a |- (
    VERINA32PostMaskWordGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ( 0 ..^ ( 2 ^ ( # ` A ) ) )
      )
      /\
      C e. Word ZZ
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( # ` C )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              ( p ` i ) < ( # ` A )
              /\
              ( C ` i ) = ( A ` ( p ` i ) )
            )
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` p ) )
            A. j e. ( 0 ..^ ( # ` p ) )
              (
                i < j
                ->
                ( p ` i ) < ( p ` j )
              )
          /\
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              ( VERINA32BitSet B k )
              <->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = k
            )
        )
      )
  ) $.
$}

${
  $d r A B $.

  verina32-post-subsequences-graph-definition $a |- (
    VERINA32PostSubsequencesGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
    )
    /\
    (
      ( # ` B ) = ( 2 ^ ( # ` A ) )
      /\
      A. r e. ( 0 ..^ ( # ` B ) )
        (
          VERINA32PostMaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina32-post-subsequences-definition $a |- (
    VERINA32PostSubsequences A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA32PostSubsequencesGraph A y )
  ) $.
$}

${
  $d i j A $.

  verina32-post-strictly-increasing-definition $a |- (
    VERINA32PostStrictlyIncreasing A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            ( A ` i ) < ( A ` j )
          )
    )
  ) $.
$}

${
  $d i j k p A B $.

  verina32-post-increasing-lens-graph-definition $a |- (
    VERINA32PostIncreasingLensGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word NN0
    )
    /\
    E. p e. Word NN0
      (
        (
          ( # ` p ) = ( # ` B )
          /\
          A. i e. ( 0 ..^ ( # ` p ) )
            (
              (
                ( p ` i )
                <
                ( # ` ( VERINA32PostSubsequences A ) )
              )
              /\
              (
                VERINA32PostStrictlyIncreasing
                  (
                    ( VERINA32PostSubsequences A )
                    ` ( p ` i )
                  )
                /\
                (
                  B ` i
                ) = (
                  # ` (
                    ( VERINA32PostSubsequences A )
                    ` ( p ` i )
                  )
                )
              )
            )
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` p ) )
            A. j e. ( 0 ..^ ( # ` p ) )
              (
                i < j
                ->
                ( p ` i ) < ( p ` j )
              )
          /\
          A. k e. (
            0 ..^ ( # ` ( VERINA32PostSubsequences A ) )
          )
            (
              (
                VERINA32PostStrictlyIncreasing
                  ( ( VERINA32PostSubsequences A ) ` k )
              )
              ->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = k
            )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina32-post-increasing-lens-definition $a |- (
    VERINA32PostIncreasingLens A
  ) = (
    iota_ y e. Word NN0
      ( VERINA32PostIncreasingLensGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina32-postcondition-definition $a |- (
    VERINA32Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    (
      B e. ran ( VERINA32PostIncreasingLens A )
      /\
      A. k e. (
        0 ..^ ( # ` ( VERINA32PostIncreasingLens A ) )
      )
        (
          ( VERINA32PostIncreasingLens A ) ` k
        ) <_ B
    )
  ) $.
$}

verina-advanced-32-longest-increasing-subsequence
  $a |- A. w e. Word ZZ
    (
      ( VERINA32Pre w )
      ->
      (
        VERINA32Post
          w
          ( VERINA32LongestIncreasingSubsequence w )
      )
    )
  $.
