$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_4 (verina__metamath__verina_advanced_4), catalog title
  LongestIncreasingSubsequence: the exact nested-loop dynamic-programming
  program returns the integer length of a longest strictly increasing
  subsequence of an arbitrary finite integer array, with its exhaustive
  maximality contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains.
  Word ZZ is exactly the type of arbitrary finite integer arrays, and
  Word ( Word ZZ ) is the type of finite lists of such arrays. For a word w,
  # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA4IntMax is exactly the source integer maximum helper.
  VERINA4DPGraph is an exact graph of the mutable nested-loop computation.
  For each outer index i, its witness s records the successive values of
  dp[i] while the inner loop visits j = 0,...,i-1. It starts at the
  Array.mkArray value one and, precisely when a[j] < a[i], changes by the
  source intMax applied to the current cell and the already-final dp[j] + 1.
  The i = 0 instance records the untouched initial cell. These well-founded
  recurrences uniquely determine exactly the final mutable array, and
  VERINA4DP selects it.

  VERINA4MaxFoldGraph reproduces dp.foldl intMax 0 entry by entry, and
  VERINA4MaxFold selects its unique integer output.
  VERINA4LongestIncreasingSubsequence preserves the source empty-array match
  explicitly and otherwise applies that fold to VERINA4DP. Thus its result is
  fixed by the executable program rather than selected from the postcondition.

  VERINA4BitSet and VERINA4MaskWordGraph give an exact indexed account of the
  source allSubseq fold
    acc ++ acc.map (fun sub => x :: sub)
  from [[]], followed by List.reverse. Mask r selects exactly input position
  k when bit k of r is one; numeric mask order is the fold's append order, and
  the selected positions occur in increasing input order after reversal.
  Hence VERINA4Subsequences preserves the order, duplicates, and all
  2^(length a) occurrences produced by that executable list computation.
  VERINA4StrictlyIncreasing is exactly List.Pairwise (<).
  VERINA4IncreasingLensGraph is the stable filter by that predicate followed
  by List.length, with each natural length canonically embedded in ZZ as
  required by the source's Int result comparison. VERINA4Post then reproduces
  List.contains and List.all without collapsing the computed list.

  VERINA4Pre is the source True precondition together with the Array Int input
  type. The proof-valued precondition argument is computationally and
  propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database has
  no $p declaration.
$)

$c
  VERINA4IntMax
  VERINA4DPGraph VERINA4DP
  VERINA4MaxFoldGraph VERINA4MaxFold
  VERINA4LongestIncreasingSubsequence VERINA4Pre
  VERINA4BitSet VERINA4MaskWordGraph
  VERINA4SubsequencesGraph VERINA4Subsequences
  VERINA4StrictlyIncreasing
  VERINA4IncreasingLensGraph VERINA4IncreasingLens
  VERINA4Post
$.

verina4-int-max-syntax
  $a class ( VERINA4IntMax A B ) $.
verina4-dp-graph-syntax
  $a wff ( VERINA4DPGraph A B ) $.
verina4-dp-syntax
  $a class ( VERINA4DP A ) $.
verina4-max-fold-graph-syntax
  $a wff ( VERINA4MaxFoldGraph A B ) $.
verina4-max-fold-syntax
  $a class ( VERINA4MaxFold A ) $.
verina4-longest-increasing-subsequence-syntax
  $a class ( VERINA4LongestIncreasingSubsequence A ) $.
verina4-precondition-syntax
  $a wff ( VERINA4Pre A ) $.
verina4-bit-set-syntax
  $a wff ( VERINA4BitSet A B ) $.
verina4-mask-word-graph-syntax
  $a wff ( VERINA4MaskWordGraph A B C ) $.
verina4-subsequences-graph-syntax
  $a wff ( VERINA4SubsequencesGraph A B ) $.
verina4-subsequences-syntax
  $a class ( VERINA4Subsequences A ) $.
verina4-strictly-increasing-syntax
  $a wff ( VERINA4StrictlyIncreasing A ) $.
verina4-increasing-lens-graph-syntax
  $a wff ( VERINA4IncreasingLensGraph A B ) $.
verina4-increasing-lens-syntax
  $a class ( VERINA4IncreasingLens A ) $.
verina4-postcondition-syntax
  $a wff ( VERINA4Post A B ) $.

verina4-int-max-definition $a |- (
  VERINA4IntMax A B
) = if (
  A < B ,
  B ,
  A
) $.

${
  $d i j s A B $.

  verina4-dp-graph-definition $a |- (
    VERINA4DPGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        E. s e. Word ZZ
          (
            (
              ( # ` s ) = ( i + 1 )
              /\
              ( s ` 0 ) = 1
            )
            /\
            (
              A. j e. ( 0 ..^ i )
                (
                  s ` ( j + 1 )
                ) = if (
                  ( A ` j ) < ( A ` i ) ,
                  (
                    VERINA4IntMax
                      ( s ` j )
                      ( ( B ` j ) + 1 )
                  ) ,
                  ( s ` j )
                )
              /\
              ( B ` i ) = ( s ` i )
            )
          )
    )
  ) $.
$}

${
  $d y A $.

  verina4-dp-definition $a |- (
    VERINA4DP A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA4DPGraph A y )
  ) $.
$}

${
  $d k s A B $.

  verina4-max-fold-graph-definition $a |- (
    VERINA4MaxFoldGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. s e. Word ZZ
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
            ) = (
              VERINA4IntMax
                ( s ` k )
                ( A ` k )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina4-max-fold-definition $a |- (
    VERINA4MaxFold A
  ) = (
    iota_ y e. ZZ
      ( VERINA4MaxFoldGraph A y )
  ) $.
$}

verina4-longest-increasing-subsequence-definition $a |- (
  VERINA4LongestIncreasingSubsequence A
) = if (
  ( VERINA4DP A ) = (/) ,
  0 ,
  ( VERINA4MaxFold ( VERINA4DP A ) )
) $.

verina4-precondition-definition $a |- (
  VERINA4Pre A
) <-> (
  A e. Word ZZ
) $.

verina4-bit-set-definition $a |- (
  VERINA4BitSet A B
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

  verina4-mask-word-graph-definition $a |- (
    VERINA4MaskWordGraph A B C
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
              ( VERINA4BitSet B k )
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

  verina4-subsequences-graph-definition $a |- (
    VERINA4SubsequencesGraph A B
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
          VERINA4MaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina4-subsequences-definition $a |- (
    VERINA4Subsequences A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA4SubsequencesGraph A y )
  ) $.
$}

${
  $d i j A $.

  verina4-strictly-increasing-definition $a |- (
    VERINA4StrictlyIncreasing A
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

  verina4-increasing-lens-graph-definition $a |- (
    VERINA4IncreasingLensGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
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
                ( # ` ( VERINA4Subsequences A ) )
              )
              /\
              (
                VERINA4StrictlyIncreasing
                  (
                    ( VERINA4Subsequences A )
                    ` ( p ` i )
                  )
                /\
                (
                  B ` i
                ) = (
                  # ` (
                    ( VERINA4Subsequences A )
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
            0 ..^ ( # ` ( VERINA4Subsequences A ) )
          )
            (
              (
                VERINA4StrictlyIncreasing
                  ( ( VERINA4Subsequences A ) ` k )
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

  verina4-increasing-lens-definition $a |- (
    VERINA4IncreasingLens A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA4IncreasingLensGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina4-postcondition-definition $a |- (
    VERINA4Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    (
      B e. ran ( VERINA4IncreasingLens A )
      /\
      A. k e. (
        0 ..^ ( # ` ( VERINA4IncreasingLens A ) )
      )
        (
          ( VERINA4IncreasingLens A ) ` k
        ) <_ B
    )
  ) $.
$}

verina-advanced-4-longest-increasing-subsequence
  $a |- A. w e. Word ZZ
    (
      ( VERINA4Pre w )
      ->
      (
        VERINA4Post
          w
          ( VERINA4LongestIncreasingSubsequence w )
      )
    )
  $.
