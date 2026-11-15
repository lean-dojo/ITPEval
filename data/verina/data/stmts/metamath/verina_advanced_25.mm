$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_25 (verina__metamath__verina_advanced_25), catalog title
  lengthOfLIS: the exact array-based dynamic-programming implementation,
  including its maximum fold, returns the maximum length of a strictly
  increasing subsequence of an arbitrary finite integer list. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains.
  Word ZZ and Word NN0 are exactly the types of arbitrary finite integer
  lists and natural-number arrays. For a word w, # ` w is its length,
  w ` k is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA25DPGraph is an exact operational graph for the mutable source
  program. For each outer-loop index i, the witness s is the trace of the
  current dp[i] through j = 0,...,i-1. It starts at the Array.mkArray value
  one and changes to dp[j] + 1 exactly when nums[j] < nums[i] and that value
  is greater than the current cell. Earlier cells dp[j] already have their
  final values, while later cells remain irrelevant. This recurrence uniquely
  gives the same final array as the nested loops and set! updates.
  VERINA25DP selects that unique final array.

  VERINA25MaxInArrayGraph reproduces the source Array.foldl from initial
  accumulator zero, using the same maximum conditional at every array entry.
  VERINA25MaxInArray selects its unique output. VERINA25LengthOfLIS preserves
  the source isEmpty branch explicitly and otherwise applies this helper to
  VERINA25DP, so it is the executable implementation rather than an output
  selected from the postcondition.

  VERINA25BitSet and VERINA25MaskWordGraph give a closed form for the source
  allSubseq fold followed by List.reverse. Mask r selects exactly input
  position k when bit k of r is one; numeric mask order is precisely the
  fold's append order, and the selected positions are restored to increasing
  input order by the final reverse. Thus VERINA25Subsequences preserves order,
  duplicates, and every one of the 2^(length nums) occurrences.
  VERINA25StrictlyIncreasing is exactly List.Pairwise (<).
  VERINA25IncreasingLensGraph is the stable filter by that predicate followed
  by the length map, and VERINA25IncreasingLens selects its unique result.

  VERINA25Pre is the source True precondition together with the List Int input
  type. VERINA25Post reproduces contains for the returned natural length and
  all for the assertion that every increasing-subsequence length is at most
  it. The proof-valued precondition argument is computationally and
  propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database has
  no $p declaration.
$)

$c
  VERINA25DPGraph VERINA25DP
  VERINA25MaxInArrayGraph VERINA25MaxInArray
  VERINA25LengthOfLIS VERINA25Pre
  VERINA25BitSet VERINA25MaskWordGraph
  VERINA25SubsequencesGraph VERINA25Subsequences
  VERINA25StrictlyIncreasing
  VERINA25IncreasingLensGraph VERINA25IncreasingLens
  VERINA25Post
$.

verina25-dp-graph-syntax
  $a wff ( VERINA25DPGraph A B ) $.
verina25-dp-syntax
  $a class ( VERINA25DP A ) $.
verina25-max-in-array-graph-syntax
  $a wff ( VERINA25MaxInArrayGraph A B ) $.
verina25-max-in-array-syntax
  $a class ( VERINA25MaxInArray A ) $.
verina25-length-of-lis-syntax
  $a class ( VERINA25LengthOfLIS A ) $.
verina25-precondition-syntax
  $a wff ( VERINA25Pre A ) $.
verina25-bit-set-syntax
  $a wff ( VERINA25BitSet A B ) $.
verina25-mask-word-graph-syntax
  $a wff ( VERINA25MaskWordGraph A B C ) $.
verina25-subsequences-graph-syntax
  $a wff ( VERINA25SubsequencesGraph A B ) $.
verina25-subsequences-syntax
  $a class ( VERINA25Subsequences A ) $.
verina25-strictly-increasing-syntax
  $a wff ( VERINA25StrictlyIncreasing A ) $.
verina25-increasing-lens-graph-syntax
  $a wff ( VERINA25IncreasingLensGraph A B ) $.
verina25-increasing-lens-syntax
  $a class ( VERINA25IncreasingLens A ) $.
verina25-postcondition-syntax
  $a wff ( VERINA25Post A B ) $.

${
  $d i j s A B $.

  verina25-dp-graph-definition $a |- (
    VERINA25DPGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word NN0
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        E. s e. Word NN0
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
                  (
                    ( A ` j ) < ( A ` i )
                    /\
                    ( s ` j ) < ( ( B ` j ) + 1 )
                  ) ,
                  ( ( B ` j ) + 1 ) ,
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

  verina25-dp-definition $a |- (
    VERINA25DP A
  ) = (
    iota_ y e. Word NN0
      ( VERINA25DPGraph A y )
  ) $.
$}

${
  $d k s A B $.

  verina25-max-in-array-graph-definition $a |- (
    VERINA25MaxInArrayGraph A B
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
          ( s ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( k + 1 )
            ) = if (
              ( s ` k ) < ( A ` k ) ,
              ( A ` k ) ,
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

  verina25-max-in-array-definition $a |- (
    VERINA25MaxInArray A
  ) = (
    iota_ y e. NN0
      ( VERINA25MaxInArrayGraph A y )
  ) $.
$}

verina25-length-of-lis-definition $a |- (
  VERINA25LengthOfLIS A
) = if (
  A = (/) ,
  0 ,
  ( VERINA25MaxInArray ( VERINA25DP A ) )
) $.

verina25-precondition-definition $a |- (
  VERINA25Pre A
) <-> (
  A e. Word ZZ
) $.

verina25-bit-set-definition $a |- (
  VERINA25BitSet A B
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

  verina25-mask-word-graph-definition $a |- (
    VERINA25MaskWordGraph A B C
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
              ( VERINA25BitSet B k )
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

  verina25-subsequences-graph-definition $a |- (
    VERINA25SubsequencesGraph A B
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
          VERINA25MaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina25-subsequences-definition $a |- (
    VERINA25Subsequences A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA25SubsequencesGraph A y )
  ) $.
$}

${
  $d i j A $.

  verina25-strictly-increasing-definition $a |- (
    VERINA25StrictlyIncreasing A
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

  verina25-increasing-lens-graph-definition $a |- (
    VERINA25IncreasingLensGraph A B
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
                ( # ` ( VERINA25Subsequences A ) )
              )
              /\
              (
                VERINA25StrictlyIncreasing
                  (
                    ( VERINA25Subsequences A )
                    ` ( p ` i )
                  )
                /\
                (
                  B ` i
                ) = (
                  # ` (
                    ( VERINA25Subsequences A )
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
            0 ..^ ( # ` ( VERINA25Subsequences A ) )
          )
            (
              (
                VERINA25StrictlyIncreasing
                  ( ( VERINA25Subsequences A ) ` k )
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

  verina25-increasing-lens-definition $a |- (
    VERINA25IncreasingLens A
  ) = (
    iota_ y e. Word NN0
      ( VERINA25IncreasingLensGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina25-postcondition-definition $a |- (
    VERINA25Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    (
      B e. ran ( VERINA25IncreasingLens A )
      /\
      A. k e. (
        0 ..^ ( # ` ( VERINA25IncreasingLens A ) )
      )
        (
          ( VERINA25IncreasingLens A ) ` k
        ) <_ B
    )
  ) $.
$}

verina-advanced-25-length-of-lis $a |- A. w e. Word ZZ
  (
    ( VERINA25Pre w )
    ->
    (
      VERINA25Post
        w
        ( VERINA25LengthOfLIS w )
    )
  )
$.
