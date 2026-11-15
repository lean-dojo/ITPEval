$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_3 (verina__metamath__verina_advanced_3), catalog title LongestCommonSubsequence: an executable
  dynamic-programming computation returns the maximum length of a common
  subsequence of two arbitrary finite integer arrays. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer arrays, viewed extensionally as zero-indexed
  words. For a word w, # ` w is its length, w ` k is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA3IntMax is the source intMax helper. VERINA3BitSet and
  VERINA3MaskWordGraph give a closed form for the source allSubseq fold:
  mask r selects precisely the input positions whose bits are one, in
  increasing position order. The masks occur in numeric order, so
  VERINA3AllSubseq is exactly the ordered, duplicate-preserving result of
  repeatedly appending acc.map (fun sub => x :: sub) and then reversing every
  sublist. VERINA3CommonLens is exactly the source filter by membership in
  the second subsequence word followed by the integer-valued length map.

  VERINA3DPGraph characterizes the complete rectangular table produced by
  the nested source loops. Its zero row and column remain initialized to
  zero; every other entry uses the diagonal-plus-one branch on equal input
  entries and VERINA3IntMax of the upper and left entries otherwise.
  These dependencies follow the source's row-major update order and uniquely
  determine the same table on every pair of typed inputs. VERINA3DP selects
  that unique table, and VERINA3LongestCommonSubsequence reads its final
  entry. Thus the target function preserves the executable implementation,
  rather than choosing an output from the postcondition.

  VERINA3Pre is the source True precondition together with the two Array Int
  input types. VERINA3Post reproduces contains and all on the exact common
  subsequence-length word. The proof-valued precondition argument is
  computationally unused and is omitted from the target function. The final
  $a declaration is the source correctness proposition; every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA3IntMax
  VERINA3BitSet
  VERINA3MaskWordGraph
  VERINA3AllSubseqGraph VERINA3AllSubseq
  VERINA3CommonLensGraph VERINA3CommonLens
  VERINA3DPGraph VERINA3DP
  VERINA3Pre VERINA3LongestCommonSubsequence VERINA3Post
$.

verina3-int-max-syntax
  $a class ( VERINA3IntMax A B ) $.
verina3-bit-set-syntax
  $a wff ( VERINA3BitSet A B ) $.
verina3-mask-word-graph-syntax
  $a wff ( VERINA3MaskWordGraph A B C ) $.
verina3-all-subseq-graph-syntax
  $a wff ( VERINA3AllSubseqGraph A B ) $.
verina3-all-subseq-syntax
  $a class ( VERINA3AllSubseq A ) $.
verina3-common-lens-graph-syntax
  $a wff ( VERINA3CommonLensGraph A B C ) $.
verina3-common-lens-syntax
  $a class ( VERINA3CommonLens A B ) $.
verina3-dp-graph-syntax
  $a wff ( VERINA3DPGraph A B C ) $.
verina3-dp-syntax
  $a class ( VERINA3DP A B ) $.
verina3-precondition-syntax
  $a wff ( VERINA3Pre A B ) $.
verina3-longest-common-subsequence-syntax
  $a class ( VERINA3LongestCommonSubsequence A B ) $.
verina3-postcondition-syntax
  $a wff ( VERINA3Post A B C ) $.

verina3-int-max-definition $a |- (
  VERINA3IntMax A B
) = if (
  A < B ,
  B ,
  A
) $.

verina3-bit-set-definition $a |- (
  VERINA3BitSet A B
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

  verina3-mask-word-graph-definition $a |- (
    VERINA3MaskWordGraph A B C
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
              ( VERINA3BitSet B k )
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

  verina3-all-subseq-graph-definition $a |- (
    VERINA3AllSubseqGraph A B
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
          VERINA3MaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina3-all-subseq-definition $a |- (
    VERINA3AllSubseq A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA3AllSubseqGraph A y )
  ) $.
$}

${
  $d i j k p A B C $.

  verina3-common-lens-graph-definition $a |- (
    VERINA3CommonLensGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
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
              (
                ( p ` i )
                <
                ( # ` ( VERINA3AllSubseq A ) )
              )
              /\
              (
                (
                  ( VERINA3AllSubseq A )
                  ` ( p ` i )
                ) e. ran ( VERINA3AllSubseq B )
                /\
                (
                  C ` i
                ) = (
                  # ` (
                    ( VERINA3AllSubseq A )
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
            0 ..^ ( # ` ( VERINA3AllSubseq A ) )
          )
            (
              (
                ( VERINA3AllSubseq A )
                ` k
              ) e. ran ( VERINA3AllSubseq B )
              ->
              E. i e. ( 0 ..^ ( # ` p ) )
                ( p ` i ) = k
            )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina3-common-lens-definition $a |- (
    VERINA3CommonLens A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA3CommonLensGraph A B y )
  ) $.
$}

${
  $d i j A B C $.

  verina3-dp-graph-definition $a |- (
    VERINA3DPGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. Word ( Word ZZ )
    )
    /\
    (
      (
        ( # ` C ) = ( ( # ` A ) + 1 )
        /\
        A. i e. ( 0 ..^ ( # ` C ) )
          (
            # ` ( C ` i )
          ) = (
            ( # ` B ) + 1
          )
      )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        A. j e. ( 0 ..^ ( # ` ( C ` i ) ) )
          (
            ( ( C ` i ) ` j )
          ) = if (
            (
              i = 0
              \/
              j = 0
            ) ,
            0 ,
            if (
              (
                A ` ( i - 1 )
              ) = (
                B ` ( j - 1 )
              ) ,
              (
                (
                  C ` ( i - 1 )
                ) ` ( j - 1 )
              ) + 1 ,
              VERINA3IntMax
                (
                  ( C ` ( i - 1 ) )
                  ` j
                )
                (
                  ( C ` i )
                  ` ( j - 1 )
                )
            )
          )
    )
  ) $.
$}

${
  $d y A B $.

  verina3-dp-definition $a |- (
    VERINA3DP A B
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA3DPGraph A B y )
  ) $.
$}

verina3-precondition-definition $a |- (
  VERINA3Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. Word ZZ
) $.

verina3-longest-common-subsequence-definition $a |- (
  VERINA3LongestCommonSubsequence A B
) = (
  (
    VERINA3DP A B
  ) ` ( # ` A )
) ` ( # ` B ) $.

${
  $d k A B C $.

  verina3-postcondition-definition $a |- (
    VERINA3Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. ZZ
    )
    /\
    (
      C e. ran ( VERINA3CommonLens A B )
      /\
      A. k e. (
        0 ..^ ( # ` ( VERINA3CommonLens A B ) )
      )
        (
          ( VERINA3CommonLens A B ) ` k
        ) <_ C
    )
  ) $.
$}

verina-advanced-3-longest-common-subsequence
  $a |- A. a e. Word ZZ
    A. b e. Word ZZ
      (
        ( VERINA3Pre a b )
        ->
        (
          VERINA3Post
            a
            b
            ( VERINA3LongestCommonSubsequence a b )
        )
      )
  $.
