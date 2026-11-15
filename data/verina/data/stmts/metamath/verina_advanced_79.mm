$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_79 (verina__metamath__verina_advanced_79), catalog title
  twoSum: the exact nested recursive search returns the lexicographically
  first pair of increasing indices whose integer entries sum to the target,
  or none when no such pair exists, with its full correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA79GetBang reproduces Lean's zero-default List.get! indexing, and
  VERINA79NatSub is truncated natural subtraction. VERINA79Drop is exactly
  List.drop. VERINA79None and VERINA79Some give disjoint tagged encodings
  used by VERINA79OptionNat and VERINA79OptionPair.

  VERINA79InnerGraph is the exact local inner recursion: on a finite suffix
  it returns the supplied starting index plus the position of the first
  entry whose sum with the fixed outer value is the target, and returns none
  exactly when no such entry exists. VERINA79OuterGraph is the exact local
  outer recursion: it tests outer positions from left to right using that
  inner computation, returns the first successful index pair, and returns
  none exactly when every outer position fails. VERINA79TwoSum invokes the
  outer recursion with index zero, independently of the postcondition.

  VERINA79Pre is the source True precondition together with the List Int and
  Int binder domains. In VERINA79Post, the none branch is exactly
  List.Pairwise failure of the target sum. The some branch preserves the
  increasing indices, bound, indexed sum, absence of a solution at every
  earlier outer index, and absence of an earlier partner for the selected
  outer index. The two finite universal clauses are bidirectionally
  equivalent to the source take/zipIdx/drop/all expressions under the stated
  index bounds. The proof-valued precondition arguments are computationally
  and propositionally unused and are represented by the explicit antecedent
  of the final correctness assertion. Every earlier $a is syntax or a
  faithful definition required by this rendering, and this database has no
  $p declaration.
$)

$c
  VERINA79GetBang VERINA79NatSub
  VERINA79None VERINA79Some
  VERINA79PairNat VERINA79OptionNat VERINA79OptionPair
  VERINA79DropGraph VERINA79Drop
  VERINA79InnerGraph VERINA79Inner
  VERINA79OuterGraph VERINA79Outer VERINA79TwoSum
  VERINA79Pre VERINA79Post
$.

verina79-get-bang-syntax
  $a class ( VERINA79GetBang A B ) $.
verina79-nat-sub-syntax
  $a class ( VERINA79NatSub A B ) $.
verina79-none-syntax
  $a class VERINA79None $.
verina79-some-syntax
  $a class ( VERINA79Some A ) $.
verina79-pair-nat-syntax
  $a class VERINA79PairNat $.
verina79-option-nat-syntax
  $a class VERINA79OptionNat $.
verina79-option-pair-syntax
  $a class VERINA79OptionPair $.
verina79-drop-graph-syntax
  $a wff ( VERINA79DropGraph A B C ) $.
verina79-drop-syntax
  $a class ( VERINA79Drop A B ) $.
verina79-inner-graph-syntax
  $a wff ( VERINA79InnerGraph A B C D E ) $.
verina79-inner-syntax
  $a class ( VERINA79Inner A B C D ) $.
verina79-outer-graph-syntax
  $a wff ( VERINA79OuterGraph A B C D ) $.
verina79-outer-syntax
  $a class ( VERINA79Outer A B C ) $.
verina79-two-sum-syntax
  $a class ( VERINA79TwoSum A B ) $.
verina79-precondition-syntax
  $a wff ( VERINA79Pre A B ) $.
verina79-postcondition-syntax
  $a wff ( VERINA79Post A B C ) $.

verina79-get-bang-definition $a |- (
  VERINA79GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verina79-nat-sub-definition $a |- (
  VERINA79NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verina79-none-definition $a |- VERINA79None = (/) $.

verina79-some-definition $a |- (
  VERINA79Some A
) = <. 1 , A >. $.

verina79-pair-nat-definition $a |- VERINA79PairNat = (
  NN0 X. NN0
) $.

${
  $d x y $.

  verina79-option-nat-definition $a |- VERINA79OptionNat =
    { x |
      (
        x = VERINA79None
        \/
        E. y e. NN0 x = ( VERINA79Some y )
      )
    } $.
$}

${
  $d p x $.

  verina79-option-pair-definition $a |- VERINA79OptionPair =
    { x |
      (
        x = VERINA79None
        \/
        E. p e. VERINA79PairNat x = ( VERINA79Some p )
      )
    } $.
$}

${
  $d k A B C $.

  verina79-drop-graph-definition $a |- (
    VERINA79DropGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      (
        # ` C
      ) = (
        VERINA79NatSub
          ( # ` A )
          B
      )
      /\
      A. k e. ( 0 ..^ ( # ` C ) )
        (
          C ` k
        ) = (
          A ` ( B + k )
        )
    )
  ) $.
$}

${
  $d y A B $.

  verina79-drop-definition $a |- (
    VERINA79Drop A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA79DropGraph A B y )
  ) $.
$}

${
  $d k m A B C D E $.

  verina79-inner-graph-definition $a |- (
    VERINA79InnerGraph A B C D E
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. ZZ
        )
        /\
        (
          C e. ZZ
          /\
          D e. NN0
        )
      )
      /\
      E e. VERINA79OptionNat
    )
    /\
    (
      E. k e. ( 0 ..^ ( # ` A ) )
        (
          (
            C + ( A ` k )
          ) = B
          /\
          (
            E = (
              VERINA79Some
                ( D + k )
            )
            /\
            A. m e. ( 0 ..^ k )
              (
                C + ( A ` m )
              ) =/= B
          )
        )
      \/
      (
        -.
        E. k e. ( 0 ..^ ( # ` A ) )
          (
            C + ( A ` k )
          ) = B
        /\
        E = VERINA79None
      )
    )
  ) $.
$}

${
  $d o A B C D $.

  verina79-inner-definition $a |- (
    VERINA79Inner A B C D
  ) = (
    iota_ o e. VERINA79OptionNat
      ( VERINA79InnerGraph A B C D o )
  ) $.
$}

${
  $d j k m A B C D $.

  verina79-outer-graph-definition $a |- (
    VERINA79OuterGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. ZZ
        )
        /\
        C e. NN0
      )
      /\
      D e. VERINA79OptionPair
    )
    /\
    (
      E. k e. ( 0 ..^ ( # ` A ) )
        E. j e. NN0
          (
            (
              VERINA79Inner
                ( VERINA79Drop A ( k + 1 ) )
                B
                ( A ` k )
                ( ( C + k ) + 1 )
            ) = (
              VERINA79Some j
            )
            /\
            (
              D = (
                VERINA79Some
                  <. ( C + k ) , j >.
              )
              /\
              A. m e. ( 0 ..^ k )
                (
                  VERINA79Inner
                    ( VERINA79Drop A ( m + 1 ) )
                    B
                    ( A ` m )
                    ( ( C + m ) + 1 )
                ) = VERINA79None
            )
          )
      \/
      (
        (
          A. m e. ( 0 ..^ ( # ` A ) )
            (
              VERINA79Inner
                ( VERINA79Drop A ( m + 1 ) )
                B
                ( A ` m )
                ( ( C + m ) + 1 )
            ) = VERINA79None
        )
        /\
        D = VERINA79None
      )
    )
  ) $.
$}

${
  $d o A B C $.

  verina79-outer-definition $a |- (
    VERINA79Outer A B C
  ) = (
    iota_ o e. VERINA79OptionPair
      ( VERINA79OuterGraph A B C o )
  ) $.
$}

verina79-two-sum-definition $a |- (
  VERINA79TwoSum A B
) = (
  VERINA79Outer A B 0
) $.

verina79-precondition-definition $a |- (
  VERINA79Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. ZZ
) $.

${
  $d i j m n A B C $.

  verina79-postcondition-definition $a |- (
    VERINA79Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. VERINA79OptionPair
    )
    /\
    (
      (
        C = VERINA79None
        /\
        A. i e. ( 0 ..^ ( # ` A ) )
          A. j e. ( ( i + 1 ) ..^ ( # ` A ) )
            (
              ( A ` i ) + ( A ` j )
            ) =/= B
      )
      \/
      E. i e. NN0 E. j e. NN0
        (
          C = (
            VERINA79Some <. i , j >.
          )
          /\
          (
            (
              i < j
              /\
              j < ( # ` A )
            )
            /\
            (
              (
                VERINA79GetBang A i
              ) + (
                VERINA79GetBang A j
              )
            ) = B
            /\
            (
              A. m e. ( 0 ..^ i )
                A. n e. ( ( m + 1 ) ..^ ( # ` A ) )
                  (
                    ( A ` m ) + ( A ` n )
                  ) =/= B
              /\
              A. n e. ( ( i + 1 ) ..^ j )
                (
                  ( VERINA79GetBang A i ) + ( A ` n )
                ) =/= B
            )
          )
        )
    )
  ) $.
$}

verina-advanced-79-two-sum $a |- A. w e. Word ZZ
  A. z e. ZZ
    (
      ( VERINA79Pre w z )
      ->
      (
        VERINA79Post
          w
          z
          ( VERINA79TwoSum w z )
      )
    )
$.
