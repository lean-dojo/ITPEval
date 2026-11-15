$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_2, catalog title LongestCommonSubsequence: an executable
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

  VERINA2IntMax is the source intMax helper. VERINA2BitSet and
  VERINA2MaskWordGraph give a closed form for the source allSubseq fold:
  mask r selects precisely the input positions whose bits are one, in
  increasing position order. The masks occur in numeric order, so
  VERINA2AllSubseq is exactly the ordered, duplicate-preserving result of
  repeatedly appending acc.map (fun sub => x :: sub) and then reversing every
  sublist. VERINA2CommonLens is exactly the source filter by membership in
  the second subsequence word followed by the integer-valued length map.

  VERINA2DPGraph characterizes the complete rectangular table produced by
  the nested source loops. Its zero row and column remain initialized to
  zero; every other entry uses the diagonal-plus-one branch on equal input
  entries and VERINA2IntMax of the upper and left entries otherwise.
  These dependencies follow the source's row-major update order and uniquely
  determine the same table on every pair of typed inputs. VERINA2DP selects
  that unique table, and VERINA2LongestCommonSubsequence reads its final
  entry. Thus the target function preserves the executable implementation,
  rather than choosing an output from the postcondition.

  VERINA2Pre is the source True precondition together with the two Array Int
  input types. VERINA2Post reproduces contains and all on the exact common
  subsequence-length word. The proof-valued precondition argument is
  computationally unused and is omitted from the target function. The final
  $a declaration is the source correctness proposition; every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA2IntMax
  VERINA2BitSet
  VERINA2MaskWordGraph
  VERINA2AllSubseqGraph VERINA2AllSubseq
  VERINA2CommonLensGraph VERINA2CommonLens
  VERINA2DPGraph VERINA2DP
  VERINA2Pre VERINA2LongestCommonSubsequence VERINA2Post
$.

verina2-int-max-syntax
  $a class ( VERINA2IntMax A B ) $.
verina2-bit-set-syntax
  $a wff ( VERINA2BitSet A B ) $.
verina2-mask-word-graph-syntax
  $a wff ( VERINA2MaskWordGraph A B C ) $.
verina2-all-subseq-graph-syntax
  $a wff ( VERINA2AllSubseqGraph A B ) $.
verina2-all-subseq-syntax
  $a class ( VERINA2AllSubseq A ) $.
verina2-common-lens-graph-syntax
  $a wff ( VERINA2CommonLensGraph A B C ) $.
verina2-common-lens-syntax
  $a class ( VERINA2CommonLens A B ) $.
verina2-dp-graph-syntax
  $a wff ( VERINA2DPGraph A B C ) $.
verina2-dp-syntax
  $a class ( VERINA2DP A B ) $.
verina2-precondition-syntax
  $a wff ( VERINA2Pre A B ) $.
verina2-longest-common-subsequence-syntax
  $a class ( VERINA2LongestCommonSubsequence A B ) $.
verina2-postcondition-syntax
  $a wff ( VERINA2Post A B C ) $.

verina2-int-max-definition $a |- (
  VERINA2IntMax A B
) = if (
  A < B ,
  B ,
  A
) $.

verina2-bit-set-definition $a |- (
  VERINA2BitSet A B
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

  verina2-mask-word-graph-definition $a |- (
    VERINA2MaskWordGraph A B C
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
              ( VERINA2BitSet B k )
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

  verina2-all-subseq-graph-definition $a |- (
    VERINA2AllSubseqGraph A B
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
          VERINA2MaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina2-all-subseq-definition $a |- (
    VERINA2AllSubseq A
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA2AllSubseqGraph A y )
  ) $.
$}

${
  $d i j k p A B C $.

  verina2-common-lens-graph-definition $a |- (
    VERINA2CommonLensGraph A B C
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
                ( # ` ( VERINA2AllSubseq A ) )
              )
              /\
              (
                (
                  ( VERINA2AllSubseq A )
                  ` ( p ` i )
                ) e. ran ( VERINA2AllSubseq B )
                /\
                (
                  C ` i
                ) = (
                  # ` (
                    ( VERINA2AllSubseq A )
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
            0 ..^ ( # ` ( VERINA2AllSubseq A ) )
          )
            (
              (
                ( VERINA2AllSubseq A )
                ` k
              ) e. ran ( VERINA2AllSubseq B )
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

  verina2-common-lens-definition $a |- (
    VERINA2CommonLens A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA2CommonLensGraph A B y )
  ) $.
$}

${
  $d i j A B C $.

  verina2-dp-graph-definition $a |- (
    VERINA2DPGraph A B C
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
              VERINA2IntMax
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

  verina2-dp-definition $a |- (
    VERINA2DP A B
  ) = (
    iota_ y e. Word ( Word ZZ )
      ( VERINA2DPGraph A B y )
  ) $.
$}

verina2-precondition-definition $a |- (
  VERINA2Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. Word ZZ
) $.

verina2-longest-common-subsequence-definition $a |- (
  VERINA2LongestCommonSubsequence A B
) = (
  (
    VERINA2DP A B
  ) ` ( # ` A )
) ` ( # ` B ) $.

${
  $d k A B C $.

  verina2-postcondition-definition $a |- (
    VERINA2Post A B C
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
      C e. ran ( VERINA2CommonLens A B )
      /\
      A. k e. (
        0 ..^ ( # ` ( VERINA2CommonLens A B ) )
      )
        (
          ( VERINA2CommonLens A B ) ` k
        ) <_ C
    )
  ) $.
$}

verina-advanced-2-longest-common-subsequence
  $a |- A. a e. Word ZZ
    A. b e. Word ZZ
      (
        ( VERINA2Pre a b )
        ->
        (
          VERINA2Post
            a
            b
            ( VERINA2LongestCommonSubsequence a b )
        )
      )
  $.
