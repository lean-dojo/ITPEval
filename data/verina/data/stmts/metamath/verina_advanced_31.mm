$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_31 (verina__metamath__verina_advanced_31), catalog title
  longestIncreasingSubseqLength: exact subsequence generation, strict-
  increase filtering, and a maximum-length fold compute the length of a
  longest strictly increasing subsequence of an arbitrary finite integer
  list. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA31BitSet and VERINA31ImplMaskWordGraph give an exact closed form for
  the source helper subsequences. Numeric mask order and the bit position
  (length - 1 - k) reproduce
    rest ++ rest.map (fun s => x :: s)
  at every recursive step, preserving the source order and duplicate
  occurrences. VERINA31ImplSubsequences selects that unique word of words.
  VERINA31ImplStrictlyIncreasing is exactly the Boolean helper's adjacent-
  comparison recursion. VERINA31ImplIncreasingGraph is its stable List.filter
  graph, and VERINA31ImplIncreasing selects the unique filtered word.

  VERINA31MaxLengthGraph threads the natural accumulator from zero through
  the filtered word and applies Nat.max to the current accumulator and list
  length at every entry, exactly reproducing the source List.foldl.
  VERINA31LongestIncreasingSubseqLength is therefore the executable program
  result, independently of the postcondition.

  The postcondition uses a separate subsequence computation in the source.
  VERINA31PostMaskWordGraph reproduces the fold
    acc ++ acc.map (fun sub => x :: sub)
  from [[]], followed by List.reverse on every result: mask bit k selects
  input position k, numeric mask order is the fold's append order, and the
  selected positions are restored to increasing input order by the reverse.
  VERINA31PostStrictlyIncreasing is exactly List.Pairwise (<).
  VERINA31PostIncreasingLensGraph is the stable filter by that predicate
  followed by the length map. VERINA31Post then reproduces List.contains for
  the returned natural length and List.all asserting that every retained
  length is at most it.

  VERINA31Pre is the source True precondition together with the List Int
  input type. The proof-valued precondition argument is computationally and
  propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database has
  no $p declaration.
$)

$c
  VERINA31BitSet
  VERINA31ImplMaskWordGraph
  VERINA31ImplSubsequencesGraph VERINA31ImplSubsequences
  VERINA31ImplStrictlyIncreasing
  VERINA31ImplIncreasingGraph VERINA31ImplIncreasing
  VERINA31MaxLengthGraph VERINA31MaxLength
  VERINA31LongestIncreasingSubseqLength VERINA31Pre
  VERINA31PostMaskWordGraph
  VERINA31PostSubsequencesGraph VERINA31PostSubsequences
  VERINA31PostStrictlyIncreasing
  VERINA31PostIncreasingLensGraph VERINA31PostIncreasingLens
  VERINA31Post
$.

verina31-bit-set-syntax
  $a wff ( VERINA31BitSet A B ) $.
verina31-impl-mask-word-graph-syntax
  $a wff ( VERINA31ImplMaskWordGraph A B C ) $.
verina31-impl-subsequences-graph-syntax
  $a wff ( VERINA31ImplSubsequencesGraph A B ) $.
verina31-impl-subsequences-syntax
  $a class ( VERINA31ImplSubsequences A ) $.
verina31-impl-strictly-increasing-syntax
  $a wff ( VERINA31ImplStrictlyIncreasing A ) $.
verina31-impl-increasing-graph-syntax
  $a wff ( VERINA31ImplIncreasingGraph A B ) $.
verina31-impl-increasing-syntax
  $a class ( VERINA31ImplIncreasing A ) $.
verina31-max-length-graph-syntax
  $a wff ( VERINA31MaxLengthGraph A B ) $.
verina31-max-length-syntax
  $a class ( VERINA31MaxLength A ) $.
verina31-longest-increasing-subseq-length-syntax
  $a class ( VERINA31LongestIncreasingSubseqLength A ) $.
verina31-precondition-syntax
  $a wff ( VERINA31Pre A ) $.
verina31-post-mask-word-graph-syntax
  $a wff ( VERINA31PostMaskWordGraph A B C ) $.
verina31-post-subsequences-graph-syntax
  $a wff ( VERINA31PostSubsequencesGraph A B ) $.
verina31-post-subsequences-syntax
  $a class ( VERINA31PostSubsequences A ) $.
verina31-post-strictly-increasing-syntax
  $a wff ( VERINA31PostStrictlyIncreasing A ) $.
verina31-post-increasing-lens-graph-syntax
  $a wff ( VERINA31PostIncreasingLensGraph A B ) $.
verina31-post-increasing-lens-syntax
  $a class ( VERINA31PostIncreasingLens A ) $.
verina31-postcondition-syntax
  $a wff ( VERINA31Post A B ) $.

verina31-bit-set-definition $a |- (
  VERINA31BitSet A B
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

  verina31-impl-mask-word-graph-definition $a |- (
    VERINA31ImplMaskWordGraph A B C
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
              (
                VERINA31BitSet
                  B
                  ( ( ( # ` A ) - 1 ) - k )
              )
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

  verina31-impl-subsequences-graph-definition $a |- (
    VERINA31ImplSubsequencesGraph A B
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
          VERINA31ImplMaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina31-impl-subsequences-definition $a |- (
    VERINA31ImplSubsequences A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA31ImplSubsequencesGraph A y )
  ) $.
$}

${
  $d i A $.

  verina31-impl-strictly-increasing-definition $a |- (
    VERINA31ImplStrictlyIncreasing A
  ) <-> (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( ( # ` A ) - 1 ) )
        ( A ` i ) < ( A ` ( i + 1 ) )
    )
  ) $.
$}

${
  $d i j k p A B $.

  verina31-impl-increasing-graph-definition $a |- (
    VERINA31ImplIncreasingGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( Word ZZ )
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
                ( # ` ( VERINA31ImplSubsequences A ) )
              )
              /\
              (
                VERINA31ImplStrictlyIncreasing
                  (
                    ( VERINA31ImplSubsequences A )
                    ` ( p ` i )
                  )
                /\
                (
                  B ` i
                ) = (
                  ( VERINA31ImplSubsequences A )
                  ` ( p ` i )
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
            0 ..^ ( # ` ( VERINA31ImplSubsequences A ) )
          )
            (
              (
                VERINA31ImplStrictlyIncreasing
                  ( ( VERINA31ImplSubsequences A ) ` k )
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

  verina31-impl-increasing-definition $a |- (
    VERINA31ImplIncreasing A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA31ImplIncreasingGraph A y )
  ) $.
$}

${
  $d k s A B $.

  verina31-max-length-graph-definition $a |- (
    VERINA31MaxLengthGraph A B
  ) <-> (
    (
      A e. Word ( Word ZZ )
      /\
      B e. NN0
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
              ( s ` k ) < ( # ` ( A ` k ) ) ,
              ( # ` ( A ` k ) ) ,
              ( s ` k )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina31-max-length-definition $a |- (
    VERINA31MaxLength A
  ) = (
    iota_ y e. NN0
      ( VERINA31MaxLengthGraph A y )
  ) $.
$}

verina31-longest-increasing-subseq-length-definition $a |- (
  VERINA31LongestIncreasingSubseqLength A
) = (
  VERINA31MaxLength ( VERINA31ImplIncreasing A )
) $.

verina31-precondition-definition $a |- (
  VERINA31Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d i j k p A B C $.

  verina31-post-mask-word-graph-definition $a |- (
    VERINA31PostMaskWordGraph A B C
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
              ( VERINA31BitSet B k )
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

  verina31-post-subsequences-graph-definition $a |- (
    VERINA31PostSubsequencesGraph A B
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
          VERINA31PostMaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina31-post-subsequences-definition $a |- (
    VERINA31PostSubsequences A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA31PostSubsequencesGraph A y )
  ) $.
$}

${
  $d i j A $.

  verina31-post-strictly-increasing-definition $a |- (
    VERINA31PostStrictlyIncreasing A
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

  verina31-post-increasing-lens-graph-definition $a |- (
    VERINA31PostIncreasingLensGraph A B
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
                ( # ` ( VERINA31PostSubsequences A ) )
              )
              /\
              (
                VERINA31PostStrictlyIncreasing
                  (
                    ( VERINA31PostSubsequences A )
                    ` ( p ` i )
                  )
                /\
                (
                  B ` i
                ) = (
                  # ` (
                    ( VERINA31PostSubsequences A )
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
            0 ..^ ( # ` ( VERINA31PostSubsequences A ) )
          )
            (
              (
                VERINA31PostStrictlyIncreasing
                  ( ( VERINA31PostSubsequences A ) ` k )
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

  verina31-post-increasing-lens-definition $a |- (
    VERINA31PostIncreasingLens A
  ) = (
    iota_ y e. Word NN0
      ( VERINA31PostIncreasingLensGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina31-postcondition-definition $a |- (
    VERINA31Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    (
      B e. ran ( VERINA31PostIncreasingLens A )
      /\
      A. k e. (
        0 ..^ ( # ` ( VERINA31PostIncreasingLens A ) )
      )
        (
          ( VERINA31PostIncreasingLens A ) ` k
        ) <_ B
    )
  ) $.
$}

verina-advanced-31-longest-increasing-subseq-length
  $a |- A. w e. Word ZZ
    (
      ( VERINA31Pre w )
      ->
      (
        VERINA31Post
          w
          ( VERINA31LongestIncreasingSubseqLength w )
      )
    )
  $.
