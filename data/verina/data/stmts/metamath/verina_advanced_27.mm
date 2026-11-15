$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_27 (verina__metamath__verina_advanced_27), catalog title
  longestCommonSubsequence: the exact recursive, left-tie-breaking program
  returns a longest common subsequence of two arbitrary Unicode strings.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINA27Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINA27Char represents arbitrary strings extensionally through both
  String.data and String.toList. VERINA27ToCharList and
  VERINA27FromCharList are therefore the source conversions, which are
  extensionally the identity on this representation.

  VERINA27ConsGraph is exact character cons. VERINA27LcsAuxGraph records the
  value of the structurally recursive source lcsAux at every pair of suffix
  positions. A boundary suffix returns the empty word. Equal heads prepend
  that character to the diagonal result. Unequal heads compare the two
  recursive result lengths and select the left result when it is at least as
  long, exactly preserving the source program's tie rule. The rectangular
  suffix table is uniquely determined, so VERINA27LcsAux selects precisely
  the executable helper output. VERINA27LongestCommonSubsequence applies the
  two source conversions around that helper; it is not selected from the
  postcondition.

  VERINA27BitSet and VERINA27MaskWordGraph give a closed form for the source
  allSubseq fold followed by List.reverse. Mask r selects exactly the input
  positions whose bits are one, in increasing position order. Numeric mask
  order is precisely the fold's append order, so VERINA27AllSubseq preserves
  the order and duplicate occurrences of the source list of subsequences.
  VERINA27CommonSubseqGraph is the exact stable filter of the first such list
  by List.contains membership in the second.

  VERINA27Pre is the source True precondition together with the two String
  input types. VERINA27Post reproduces contains for the returned string and
  all for the assertion that every common subsequence has length at most the
  result. The proof-valued precondition argument is computationally and
  propositionally unused and is omitted from the target function and
  predicate. The final $a declaration is the source correctness proposition.
  Every earlier $a is syntax or a faithful definition, and this database has
  no $p declaration.
$)

$c
  VERINA27Char
  VERINA27ToCharList VERINA27FromCharList
  VERINA27ConsGraph
  VERINA27LcsAuxGraph VERINA27LcsAux
  VERINA27LongestCommonSubsequence VERINA27Pre
  VERINA27BitSet VERINA27MaskWordGraph
  VERINA27AllSubseqGraph VERINA27AllSubseq
  VERINA27CommonSubseqGraph VERINA27CommonSubseq
  VERINA27Post
$.

verina27-char-syntax
  $a class VERINA27Char $.
verina27-to-char-list-syntax
  $a class ( VERINA27ToCharList A ) $.
verina27-from-char-list-syntax
  $a class ( VERINA27FromCharList A ) $.
verina27-cons-graph-syntax
  $a wff ( VERINA27ConsGraph A B C ) $.
verina27-lcs-aux-graph-syntax
  $a wff ( VERINA27LcsAuxGraph A B C ) $.
verina27-lcs-aux-syntax
  $a class ( VERINA27LcsAux A B ) $.
verina27-longest-common-subsequence-syntax
  $a class ( VERINA27LongestCommonSubsequence A B ) $.
verina27-precondition-syntax
  $a wff ( VERINA27Pre A B ) $.
verina27-bit-set-syntax
  $a wff ( VERINA27BitSet A B ) $.
verina27-mask-word-graph-syntax
  $a wff ( VERINA27MaskWordGraph A B C ) $.
verina27-all-subseq-graph-syntax
  $a wff ( VERINA27AllSubseqGraph A B ) $.
verina27-all-subseq-syntax
  $a class ( VERINA27AllSubseq A ) $.
verina27-common-subseq-graph-syntax
  $a wff ( VERINA27CommonSubseqGraph A B C ) $.
verina27-common-subseq-syntax
  $a class ( VERINA27CommonSubseq A B ) $.
verina27-postcondition-syntax
  $a wff ( VERINA27Post A B C ) $.

verina27-char-definition $a |- VERINA27Char =
  { x e. NN0 |
    (
      x < ; ; ; ; ; ; 1 1 1 4 1 1 2
      /\
      (
        x < ; ; ; ; 5 5 2 9 6
        \/
        ; ; ; ; 5 7 3 4 3 < x
      )
    )
  } $.

verina27-to-char-list-definition $a |- (
  VERINA27ToCharList A
) = A $.

verina27-from-char-list-definition $a |- (
  VERINA27FromCharList A
) = A $.

${
  $d k A B C $.

  verina27-cons-graph-definition $a |- (
    VERINA27ConsGraph A B C
  ) <-> (
    (
      (
        A e. VERINA27Char
        /\
        B e. Word VERINA27Char
      )
      /\
      C e. Word VERINA27Char
    )
    /\
    (
      ( # ` C ) = ( ( # ` B ) + 1 )
      /\
      A. k e. ( 0 ..^ ( # ` C ) )
        (
          C ` k
        ) = if (
          k = 0 ,
          A ,
          B ` ( k - 1 )
        )
    )
  ) $.
$}

${
  $d i j t A B C $.

  verina27-lcs-aux-graph-definition $a |- (
    VERINA27LcsAuxGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA27Char
        /\
        B e. Word VERINA27Char
      )
      /\
      C e. Word VERINA27Char
    )
    /\
    E. t e. Word ( Word ( Word VERINA27Char ) )
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          A. i e. ( 0 ..^ ( # ` t ) )
            (
              # ` ( t ` i )
            ) = (
              ( # ` B ) + 1
            )
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` t ) )
            A. j e. ( 0 ..^ ( # ` ( t ` i ) ) )
              (
                (
                  (
                    (
                      i = ( # ` A )
                      \/
                      j = ( # ` B )
                    )
                    /\
                    ( ( t ` i ) ` j ) = (/)
                  )
                  \/
                  (
                    (
                      i < ( # ` A )
                      /\
                      j < ( # ` B )
                    )
                    /\
                    (
                      (
                        (
                          A ` i
                        ) = (
                          B ` j
                        )
                        /\
                        (
                          VERINA27ConsGraph
                            ( A ` i )
                            ( ( t ` ( i + 1 ) ) ` ( j + 1 ) )
                            ( ( t ` i ) ` j )
                        )
                      )
                      \/
                      (
                        (
                          A ` i
                        ) =/= (
                          B ` j
                        )
                        /\
                        (
                          (
                            (
                              # ` ( ( t ` i ) ` ( j + 1 ) )
                            ) <_ (
                              # ` ( ( t ` ( i + 1 ) ) ` j )
                            )
                            /\
                            (
                              ( t ` i ) ` j
                            ) = (
                              ( t ` ( i + 1 ) ) ` j
                            )
                          )
                          \/
                          (
                            (
                              # ` ( ( t ` ( i + 1 ) ) ` j )
                            ) < (
                              # ` ( ( t ` i ) ` ( j + 1 ) )
                            )
                            /\
                            (
                              ( t ` i ) ` j
                            ) = (
                              ( t ` i ) ` ( j + 1 )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
          /\
          C = ( ( t ` 0 ) ` 0 )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina27-lcs-aux-definition $a |- (
    VERINA27LcsAux A B
  ) = (
    iota_ y e. Word VERINA27Char
      ( VERINA27LcsAuxGraph A B y )
  ) $.
$}

verina27-longest-common-subsequence-definition $a |- (
  VERINA27LongestCommonSubsequence A B
) = (
  VERINA27FromCharList
    (
      VERINA27LcsAux
        ( VERINA27ToCharList A )
        ( VERINA27ToCharList B )
    )
) $.

verina27-precondition-definition $a |- (
  VERINA27Pre A B
) <-> (
  A e. Word VERINA27Char
  /\
  B e. Word VERINA27Char
) $.

verina27-bit-set-definition $a |- (
  VERINA27BitSet A B
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

  verina27-mask-word-graph-definition $a |- (
    VERINA27MaskWordGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA27Char
        /\
        B e. ( 0 ..^ ( 2 ^ ( # ` A ) ) )
      )
      /\
      C e. Word VERINA27Char
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
              ( VERINA27BitSet B k )
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

  verina27-all-subseq-graph-definition $a |- (
    VERINA27AllSubseqGraph A B
  ) <-> (
    (
      A e. Word VERINA27Char
      /\
      B e. Word ( Word VERINA27Char )
    )
    /\
    (
      ( # ` B ) = ( 2 ^ ( # ` A ) )
      /\
      A. r e. ( 0 ..^ ( # ` B ) )
        (
          VERINA27MaskWordGraph
            A
            r
            ( B ` r )
        )
    )
  ) $.
$}

${
  $d y A $.

  verina27-all-subseq-definition $a |- (
    VERINA27AllSubseq A
  ) = (
    iota_ y e. Word ( Word VERINA27Char )
      ( VERINA27AllSubseqGraph A y )
  ) $.
$}

${
  $d i j k p A B C $.

  verina27-common-subseq-graph-definition $a |- (
    VERINA27CommonSubseqGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINA27Char
        /\
        B e. Word VERINA27Char
      )
      /\
      C e. Word ( Word VERINA27Char )
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
                ( # ` ( VERINA27AllSubseq A ) )
              )
              /\
              (
                (
                  ( VERINA27AllSubseq A )
                  ` ( p ` i )
                ) e. ran ( VERINA27AllSubseq B )
                /\
                (
                  C ` i
                ) = (
                  ( VERINA27AllSubseq A )
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
            0 ..^ ( # ` ( VERINA27AllSubseq A ) )
          )
            (
              (
                ( VERINA27AllSubseq A )
                ` k
              ) e. ran ( VERINA27AllSubseq B )
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

  verina27-common-subseq-definition $a |- (
    VERINA27CommonSubseq A B
  ) = (
    iota_ y e. Word ( Word VERINA27Char )
      ( VERINA27CommonSubseqGraph A B y )
  ) $.
$}

${
  $d k A B C $.

  verina27-postcondition-definition $a |- (
    VERINA27Post A B C
  ) <-> (
    (
      (
        A e. Word VERINA27Char
        /\
        B e. Word VERINA27Char
      )
      /\
      C e. Word VERINA27Char
    )
    /\
    (
      C e. ran ( VERINA27CommonSubseq A B )
      /\
      A. k e. (
        0 ..^ ( # ` ( VERINA27CommonSubseq A B ) )
      )
        (
          # ` (
            ( VERINA27CommonSubseq A B ) ` k
          )
        ) <_ (
          # ` C
        )
    )
  ) $.
$}

verina-advanced-27-longest-common-subsequence
  $a |- A. a e. Word VERINA27Char
    A. b e. Word VERINA27Char
      (
        ( VERINA27Pre a b )
        ->
        (
          VERINA27Post
            a
            b
            ( VERINA27LongestCommonSubsequence a b )
        )
      )
  $.
