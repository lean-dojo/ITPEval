$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_33 (verina__metamath__verina_advanced_33), catalog title
  longestIncreasingSubsequence: the exact recursive take-or-skip program
  computes the natural-number length of a longest strictly increasing
  subsequence of an arbitrary finite integer list, with its maximality
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA33NatMax is the source max2 helper. VERINA33ListLength is the source
  listLength helper, extensionally represented by SetMM word length; the
  source declares it locally but never calls it. VERINA33None,
  VERINA33Some, and VERINA33OptionInt give a disjoint tagged encoding of
  Option Int.

  VERINA33HelperGraph is the exact finite execution graph of the source
  structurally recursive helper on every integer word and optional previous
  value. In its witnesses, u[i] is the value on the suffix beginning at i
  with previous value none. The triangular table t[p][i], for p < i, is the
  value on that suffix with previous value some input[p]. These entries
  reproduce both recursive calls after taking or skipping input[i], including
  the strict comparison, the zero withTake value when taking is disallowed,
  and the source max2 branch. For an arbitrary external some x, q[i] records
  the analogous suffix trace using x on every skip branch and the same t row
  after a take. All traces end at zero on the empty suffix.

  VERINA33Helper selects the unique result of that operational graph, and
  VERINA33LongestIncreasingSubsequence calls it with none exactly as the
  executable implementation does. It is not selected from the postcondition.

  VERINA33BitSet and VERINA33PostMaskWordGraph reproduce the postcondition's
  fold
    acc ++ acc.map (fun sub => x :: sub)
  from [[]], followed by List.reverse on every result: mask bit k selects
  input position k, numeric mask order is the fold's append order, and the
  selected positions occur in increasing input order after the reverse.
  VERINA33PostStrictlyIncreasing is exactly List.Pairwise (<).
  VERINA33PostIncreasingLensGraph is the stable filter by that predicate
  followed by the natural-number length map. VERINA33Post then reproduces
  List.contains for the returned length and List.all asserting that every
  retained length is at most it.

  VERINA33Pre is the source True precondition together with the List Int
  input type. The proof-valued precondition argument is computationally and
  propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database has
  no $p declaration.
$)

$c
  VERINA33NatMax
  VERINA33ListLength
  VERINA33None VERINA33Some VERINA33OptionInt
  VERINA33HelperGraph VERINA33Helper
  VERINA33LongestIncreasingSubsequence VERINA33Pre
  VERINA33BitSet
  VERINA33PostMaskWordGraph
  VERINA33PostSubsequencesGraph VERINA33PostSubsequences
  VERINA33PostStrictlyIncreasing
  VERINA33PostIncreasingLensGraph VERINA33PostIncreasingLens
  VERINA33Post
$.

verina33-nat-max-syntax
  $a class ( VERINA33NatMax A B ) $.
verina33-list-length-syntax
  $a class ( VERINA33ListLength A ) $.
verina33-none-syntax
  $a class VERINA33None $.
verina33-some-syntax
  $a class ( VERINA33Some A ) $.
verina33-option-int-syntax
  $a class VERINA33OptionInt $.
verina33-helper-graph-syntax
  $a wff ( VERINA33HelperGraph A B C ) $.
verina33-helper-syntax
  $a class ( VERINA33Helper A B ) $.
verina33-longest-increasing-subsequence-syntax
  $a class ( VERINA33LongestIncreasingSubsequence A ) $.
verina33-precondition-syntax
  $a wff ( VERINA33Pre A ) $.
verina33-bit-set-syntax
  $a wff ( VERINA33BitSet A B ) $.
verina33-post-mask-word-graph-syntax
  $a wff ( VERINA33PostMaskWordGraph A B C ) $.
verina33-post-subsequences-graph-syntax
  $a wff ( VERINA33PostSubsequencesGraph A B ) $.
verina33-post-subsequences-syntax
  $a class ( VERINA33PostSubsequences A ) $.
verina33-post-strictly-increasing-syntax
  $a wff ( VERINA33PostStrictlyIncreasing A ) $.
verina33-post-increasing-lens-graph-syntax
  $a wff ( VERINA33PostIncreasingLensGraph A B ) $.
verina33-post-increasing-lens-syntax
  $a class ( VERINA33PostIncreasingLens A ) $.
verina33-postcondition-syntax
  $a wff ( VERINA33Post A B ) $.

verina33-nat-max-definition $a |- (
  VERINA33NatMax A B
) = if (
  B < A ,
  A ,
  B
) $.

verina33-list-length-definition $a |- (
  VERINA33ListLength A
) = ( # ` A ) $.

verina33-none-definition $a |- VERINA33None = (/) $.

verina33-some-definition $a |- (
  VERINA33Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina33-option-int-definition $a |- VERINA33OptionInt =
    { x |
      (
        x = VERINA33None
        \/
        E. y e. ZZ x = ( VERINA33Some y )
      )
    } $.
$}

${
  $d i p q t u x A B C $.

  verina33-helper-graph-definition $a |- (
    VERINA33HelperGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. VERINA33OptionInt
      )
      /\
      C e. NN0
    )
    /\
    E. t e. Word ( Word NN0 )
      E. u e. Word NN0
      (
        (
          (
            ( # ` t ) = ( # ` A )
            /\
            A. p e. ( 0 ..^ ( # ` A ) )
              (
                # ` ( t ` p )
              ) = (
                ( # ` A ) + 1
              )
          )
          /\
          (
            (
              ( # ` u ) = ( ( # ` A ) + 1 )
              /\
              ( u ` ( # ` A ) ) = 0
            )
            /\
            A. p e. ( 0 ..^ ( # ` A ) )
              (
                ( t ` p ) ` ( # ` A )
              ) = 0
          )
        )
        /\
        (
          (
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                u ` i
              ) = (
                VERINA33NatMax
                  (
                    1 +
                    ( ( t ` i ) ` ( i + 1 ) )
                  )
                  ( u ` ( i + 1 ) )
              )
            /\
            A. p e. ( 0 ..^ ( # ` A ) )
              A. i e. ( ( p + 1 ) ..^ ( # ` A ) )
                (
                  ( t ` p ) ` i
                ) = (
                  VERINA33NatMax
                    if (
                      ( A ` p ) < ( A ` i ) ,
                      (
                        1 +
                        ( ( t ` i ) ` ( i + 1 ) )
                      ) ,
                      0
                    )
                    ( ( t ` p ) ` ( i + 1 ) )
                )
          )
          /\
          (
            (
              B = VERINA33None
              /\
              C = ( u ` 0 )
            )
            \/
            E. x e. ZZ
              E. q e. Word NN0
                (
                  (
                    (
                      B = ( VERINA33Some x )
                      /\
                      ( # ` q ) = ( ( # ` A ) + 1 )
                    )
                    /\
                    ( q ` ( # ` A ) ) = 0
                  )
                  /\
                  (
                    A. i e. ( 0 ..^ ( # ` A ) )
                      (
                        q ` i
                      ) = (
                        VERINA33NatMax
                          if (
                            x < ( A ` i ) ,
                            (
                              1 +
                              ( ( t ` i ) ` ( i + 1 ) )
                            ) ,
                            0
                          )
                          ( q ` ( i + 1 ) )
                      )
                    /\
                    C = ( q ` 0 )
                  )
                )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina33-helper-definition $a |- (
    VERINA33Helper A B
  ) = (
    iota_ y e. NN0
      ( VERINA33HelperGraph A B y )
  ) $.
$}

verina33-longest-increasing-subsequence-definition $a |- (
  VERINA33LongestIncreasingSubsequence A
) = (
  VERINA33Helper A VERINA33None
) $.

verina33-precondition-definition $a |- (
  VERINA33Pre A
) <-> (
  A e. Word ZZ
) $.

verina33-bit-set-definition $a |- (
  VERINA33BitSet A B
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

  verina33-post-mask-word-graph-definition $a |- (
    VERINA33PostMaskWordGraph A B C
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
              ( VERINA33BitSet B k )
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

  verina33-post-subsequences-graph-definition $a |- (
    VERINA33PostSubsequencesGraph A B
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
          VERINA33PostMaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina33-post-subsequences-definition $a |- (
    VERINA33PostSubsequences A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA33PostSubsequencesGraph A y )
  ) $.
$}

${
  $d i j A $.

  verina33-post-strictly-increasing-definition $a |- (
    VERINA33PostStrictlyIncreasing A
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

  verina33-post-increasing-lens-graph-definition $a |- (
    VERINA33PostIncreasingLensGraph A B
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
                ( # ` ( VERINA33PostSubsequences A ) )
              )
              /\
              (
                VERINA33PostStrictlyIncreasing
                  (
                    ( VERINA33PostSubsequences A )
                    ` ( p ` i )
                  )
                /\
                (
                  B ` i
                ) = (
                  # ` (
                    ( VERINA33PostSubsequences A )
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
            0 ..^ ( # ` ( VERINA33PostSubsequences A ) )
          )
            (
              (
                VERINA33PostStrictlyIncreasing
                  ( ( VERINA33PostSubsequences A ) ` k )
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

  verina33-post-increasing-lens-definition $a |- (
    VERINA33PostIncreasingLens A
  ) = (
    iota_ y e. Word NN0
      ( VERINA33PostIncreasingLensGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina33-postcondition-definition $a |- (
    VERINA33Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. NN0
    )
    /\
    (
      B e. ran ( VERINA33PostIncreasingLens A )
      /\
      A. k e. (
        0 ..^ ( # ` ( VERINA33PostIncreasingLens A ) )
      )
        (
          ( VERINA33PostIncreasingLens A ) ` k
        ) <_ B
    )
  ) $.
$}

verina-advanced-33-longest-increasing-subsequence
  $a |- A. w e. Word ZZ
    (
      ( VERINA33Pre w )
      ->
      (
        VERINA33Post
          w
          ( VERINA33LongestIncreasingSubsequence w )
      )
    )
  $.
