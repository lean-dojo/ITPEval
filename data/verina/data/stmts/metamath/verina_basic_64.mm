$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_64
  (verina__metamath__verina_basic_64), catalog title insert: the exact
  executable three-pass character-array program inserts a specified prefix of
  one finite array into another at the designated position and satisfies its
  size, prefix, inserted-segment, and shifted-suffix contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB64Char is exactly Lean's Char domain of Unicode scalar values, and
  Word VERINAB64Char is exactly the type of arbitrary finite character
  arrays. For a word w, # ` w is its natural-number size, w ` k is zero-based
  lookup, and 0 ..^ n is the set of natural indices traversed by Array.range
  n. The Unicode scalar value 32 is Lean's space character.

  VERINAB64NatSub is Lean's truncated natural subtraction.
  VERINAB64GetBang reproduces Array.get! on character arrays, including the
  inhabited default character with scalar value zero outside the array.
  VERINAB64SetBangGraph and its iota-selected function reproduce Array.set!,
  including unchanged-array behavior at an out-of-range index.
  VERINAB64BlankArray is exactly Array.mkArray n ' '.

  VERINAB64PrefixGraph is the exact execution trace of the first Array.foldl
  over Array.range l: transition k writes oline[k]! at k precisely when
  k < atPos. VERINAB64NewGraph is the exact trace of the second fold: its
  transition k writes nl[k]! at atPos + k. VERINAB64SuffixGraph is the exact
  trace of the third fold: transition k writes oline[k]! at k + p precisely
  when k >= atPos. Their iota-selected functions therefore fix the same
  unique intermediate and final arrays as the source program, in the same
  left-to-right order, without admitting additional outputs.

  VERINAB64Pre preserves the three source bounds. VERINAB64Insert composes the
  blank-array initialization and the three folds exactly. VERINAB64Post
  preserves the result-size equation and the three List.range all conditions,
  with get! retained explicitly. The proof-valued precondition arguments to
  the implementation and postcondition are computationally and
  propositionally unused beyond the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB64Char VERINAB64NatSub VERINAB64GetBang
  VERINAB64SetBangGraph VERINAB64SetBang
  VERINAB64BlankArrayGraph VERINAB64BlankArray
  VERINAB64PrefixGraph VERINAB64Prefix
  VERINAB64NewGraph VERINAB64New
  VERINAB64SuffixGraph VERINAB64Suffix
  VERINAB64Pre VERINAB64Insert VERINAB64Post
$.

verinab64-char-syntax
  $a class VERINAB64Char $.
verinab64-nat-sub-syntax
  $a class ( VERINAB64NatSub A B ) $.
verinab64-get-bang-syntax
  $a class ( VERINAB64GetBang A B ) $.
verinab64-set-bang-graph-syntax
  $a wff ( VERINAB64SetBangGraph A B C D ) $.
verinab64-set-bang-syntax
  $a class ( VERINAB64SetBang A B C ) $.
verinab64-blank-array-graph-syntax
  $a wff ( VERINAB64BlankArrayGraph A B ) $.
verinab64-blank-array-syntax
  $a class ( VERINAB64BlankArray A ) $.
verinab64-prefix-graph-syntax
  $a wff ( VERINAB64PrefixGraph A B C D E ) $.
verinab64-prefix-syntax
  $a class ( VERINAB64Prefix A B C D ) $.
verinab64-new-graph-syntax
  $a wff ( VERINAB64NewGraph A B C D E ) $.
verinab64-new-syntax
  $a class ( VERINAB64New A B C D ) $.
verinab64-suffix-graph-syntax
  $a wff ( VERINAB64SuffixGraph A B C D E F ) $.
verinab64-suffix-syntax
  $a class ( VERINAB64Suffix A B C D E ) $.
verinab64-precondition-syntax
  $a wff ( VERINAB64Pre A B C D E ) $.
verinab64-program-syntax
  $a class ( VERINAB64Insert A B C D E ) $.
verinab64-postcondition-syntax
  $a wff ( VERINAB64Post A B C D E F ) $.

verinab64-char-definition $a |- VERINAB64Char =
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

verinab64-nat-sub-definition $a |- (
  VERINAB64NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab64-get-bang-definition $a |- (
  VERINAB64GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B C D $.

  verinab64-set-bang-graph-definition $a |- (
    VERINAB64SetBangGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word VERINAB64Char
          /\
          B e. NN0
        )
        /\
        C e. VERINAB64Char
      )
      /\
      D e. Word VERINAB64Char
    )
    /\
    (
      ( # ` D ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        ( D ` k ) = if (
          k = B ,
          C ,
          ( A ` k )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab64-set-bang-definition $a |- (
    VERINAB64SetBang A B C
  ) = (
    iota_ y e. Word VERINAB64Char
      ( VERINAB64SetBangGraph A B C y )
  ) $.
$}

${
  $d k A B $.

  verinab64-blank-array-graph-definition $a |- (
    VERINAB64BlankArrayGraph A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. Word VERINAB64Char
    )
    /\
    (
      ( # ` B ) = A
      /\
      A. k e. ( 0 ..^ A )
        ( B ` k ) = ( ; 3 2 )
    )
  ) $.
$}

${
  $d y A $.

  verinab64-blank-array-definition $a |- (
    VERINAB64BlankArray A
  ) = (
    iota_ y e. Word VERINAB64Char
      ( VERINAB64BlankArrayGraph A y )
  ) $.
$}

${
  $d k t A B C D E $.

  verinab64-prefix-graph-definition $a |- (
    VERINAB64PrefixGraph A B C D E
  ) <-> (
    (
      (
        (
          (
            A e. Word VERINAB64Char
            /\
            B e. NN0
          )
          /\
          C e. NN0
        )
        /\
        D e. Word VERINAB64Char
      )
      /\
      E e. Word VERINAB64Char
    )
    /\
    E. t e. Word ( Word VERINAB64Char )
      (
        (
          ( # ` t ) = ( B + 1 )
          /\
          ( t ` 0 ) = D
        )
        /\
        (
          A. k e. ( 0 ..^ B )
            (
              t ` ( k + 1 )
            ) = if (
              k < C ,
              (
                VERINAB64SetBang
                  ( t ` k )
                  k
                  ( VERINAB64GetBang A k )
              ) ,
              ( t ` k )
            )
          /\
          E = ( t ` B )
        )
      )
  ) $.
$}

${
  $d y A B C D $.

  verinab64-prefix-definition $a |- (
    VERINAB64Prefix A B C D
  ) = (
    iota_ y e. Word VERINAB64Char
      ( VERINAB64PrefixGraph A B C D y )
  ) $.
$}

${
  $d k t A B C D E $.

  verinab64-new-graph-definition $a |- (
    VERINAB64NewGraph A B C D E
  ) <-> (
    (
      (
        (
          (
            A e. Word VERINAB64Char
            /\
            B e. NN0
          )
          /\
          C e. NN0
        )
        /\
        D e. Word VERINAB64Char
      )
      /\
      E e. Word VERINAB64Char
    )
    /\
    E. t e. Word ( Word VERINAB64Char )
      (
        (
          ( # ` t ) = ( B + 1 )
          /\
          ( t ` 0 ) = D
        )
        /\
        (
          A. k e. ( 0 ..^ B )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB64SetBang
                ( t ` k )
                ( C + k )
                ( VERINAB64GetBang A k )
            )
          /\
          E = ( t ` B )
        )
      )
  ) $.
$}

${
  $d y A B C D $.

  verinab64-new-definition $a |- (
    VERINAB64New A B C D
  ) = (
    iota_ y e. Word VERINAB64Char
      ( VERINAB64NewGraph A B C D y )
  ) $.
$}

${
  $d k t A B C D E F $.

  verinab64-suffix-graph-definition $a |- (
    VERINAB64SuffixGraph A B C D E F
  ) <-> (
    (
      (
        (
          (
            (
              A e. Word VERINAB64Char
              /\
              B e. NN0
            )
            /\
            C e. NN0
          )
          /\
          D e. NN0
        )
        /\
        E e. Word VERINAB64Char
      )
      /\
      F e. Word VERINAB64Char
    )
    /\
    E. t e. Word ( Word VERINAB64Char )
      (
        (
          ( # ` t ) = ( B + 1 )
          /\
          ( t ` 0 ) = E
        )
        /\
        (
          A. k e. ( 0 ..^ B )
            (
              t ` ( k + 1 )
            ) = if (
              D <_ k ,
              (
                VERINAB64SetBang
                  ( t ` k )
                  ( k + C )
                  ( VERINAB64GetBang A k )
              ) ,
              ( t ` k )
            )
          /\
          F = ( t ` B )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verinab64-suffix-definition $a |- (
    VERINAB64Suffix A B C D E
  ) = (
    iota_ y e. Word VERINAB64Char
      ( VERINAB64SuffixGraph A B C D E y )
  ) $.
$}

verinab64-precondition-definition $a |- (
  VERINAB64Pre A B C D E
) <-> (
  (
    (
      (
        A e. Word VERINAB64Char
        /\
        B e. NN0
      )
      /\
      C e. Word VERINAB64Char
    )
    /\
    (
      D e. NN0
      /\
      E e. NN0
    )
  )
  /\
  (
    B <_ ( # ` A )
    /\
    (
      D <_ ( # ` C )
      /\
      E <_ B
    )
  )
) $.

verinab64-program-definition $a |- (
  VERINAB64Insert A B C D E
) = (
  VERINAB64Suffix
    A
    B
    D
    E
    (
      VERINAB64New
        C
        D
        E
        (
          VERINAB64Prefix
            A
            B
            E
            ( VERINAB64BlankArray ( B + D ) )
        )
    )
) $.

${
  $d i A B C D E F $.

  verinab64-postcondition-definition $a |- (
    VERINAB64Post A B C D E F
  ) <-> (
    (
      (
        (
          (
            (
              A e. Word VERINAB64Char
              /\
              B e. NN0
            )
            /\
            C e. Word VERINAB64Char
          )
          /\
          (
            D e. NN0
            /\
            E e. NN0
          )
        )
        /\
        F e. Word VERINAB64Char
      )
      /\
      ( # ` F ) = ( B + D )
    )
    /\
    (
      A. i e. ( 0 ..^ D )
        (
          VERINAB64GetBang F ( E + i )
        ) = (
          VERINAB64GetBang C i
        )
      /\
      (
        A. i e. ( 0 ..^ E )
          (
            VERINAB64GetBang F i
          ) = (
            VERINAB64GetBang A i
          )
        /\
        A. i e. (
          0 ..^ ( VERINAB64NatSub B E )
        )
          (
            VERINAB64GetBang F ( ( E + D ) + i )
          ) = (
            VERINAB64GetBang A ( E + i )
          )
      )
    )
  ) $.
$}

verina-basic-64-insert $a |-
  A. o e. Word VERINAB64Char
    A. l e. NN0
      A. n e. Word VERINAB64Char
        A. p e. NN0
          A. a e. NN0
            (
              ( VERINAB64Pre o l n p a )
              ->
              (
                VERINAB64Post
                  o
                  l
                  n
                  p
                  a
                  ( VERINAB64Insert o l n p a )
              )
            )
$.
