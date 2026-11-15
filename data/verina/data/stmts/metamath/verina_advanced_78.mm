$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_78 (verina__metamath__verina_advanced_78), catalog title
  twoSum: the exact recursive complement-search program returns increasing
  indices of the unique pair of integers whose sum is the target, under the
  complete precondition and postcondition contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA78GetBang reproduces Lean's zero-default List.get! indexing.
  VERINA78NatSub is truncated natural subtraction. VERINA78PairRank maps an
  index pair i < j to its position in the source List.range/flatMap/drop/map
  order, and VERINA78PairwiseSumsGraph fixes every entry of that exact word.
  VERINA78Count is List.count, so VERINA78Pre is precisely the length-greater-
  than-one and unique-pairwise-sum precondition, together with the source
  List Int and Int binder domains.

  VERINA78None, VERINA78Some, and VERINA78OptionNat give a disjoint tagged
  encoding of Option Nat. VERINA78Drop is exactly List.drop.
  VERINA78FindComplementAuxGraph selects the first matching entry of its
  input word and returns i + j + offset + 1, or none when no entry matches.
  VERINA78FindComplement invokes that local recursion with offset zero.

  VERINA78TwoSumAuxGraph selects the first remaining outer position whose
  call to VERINA78FindComplement succeeds and returns the corresponding
  index pair. If every such call returns none, it returns (0, 0), which is
  the result component of Lean's inhabited-default panic on the empty case.
  Thus VERINA78TwoSumAux is the exact source recursion on every typed input,
  and VERINA78TwoSum invokes it at outer index zero independently of the
  postcondition.

  VERINA78Post preserves the increasing-index, both-bounds, and indexed-sum
  clauses. The proof-valued precondition arguments to twoSum and the
  postcondition are computationally and propositionally unused, so the
  explicit antecedent of the final correctness assertion represents them.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINA78GetBang VERINA78NatSub
  VERINA78PairRank
  VERINA78PairwiseSumsGraph VERINA78PairwiseSums VERINA78Count
  VERINA78None VERINA78Some VERINA78OptionNat
  VERINA78DropGraph VERINA78Drop
  VERINA78FindComplementAuxGraph VERINA78FindComplement
  VERINA78PairNat
  VERINA78TwoSumAuxGraph VERINA78TwoSumAux VERINA78TwoSum
  VERINA78Pre VERINA78Post
$.

verina78-get-bang-syntax
  $a class ( VERINA78GetBang A B ) $.
verina78-nat-sub-syntax
  $a class ( VERINA78NatSub A B ) $.
verina78-pair-rank-syntax
  $a class ( VERINA78PairRank A B C ) $.
verina78-pairwise-sums-graph-syntax
  $a wff ( VERINA78PairwiseSumsGraph A B ) $.
verina78-pairwise-sums-syntax
  $a class ( VERINA78PairwiseSums A ) $.
verina78-count-syntax
  $a class ( VERINA78Count A B ) $.
verina78-none-syntax
  $a class VERINA78None $.
verina78-some-syntax
  $a class ( VERINA78Some A ) $.
verina78-option-nat-syntax
  $a class VERINA78OptionNat $.
verina78-drop-graph-syntax
  $a wff ( VERINA78DropGraph A B C ) $.
verina78-drop-syntax
  $a class ( VERINA78Drop A B ) $.
verina78-find-complement-aux-graph-syntax
  $a wff ( VERINA78FindComplementAuxGraph A B C D E F ) $.
verina78-find-complement-syntax
  $a class ( VERINA78FindComplement A B C D ) $.
verina78-pair-nat-syntax
  $a class VERINA78PairNat $.
verina78-two-sum-aux-graph-syntax
  $a wff ( VERINA78TwoSumAuxGraph A B C D ) $.
verina78-two-sum-aux-syntax
  $a class ( VERINA78TwoSumAux A B C ) $.
verina78-two-sum-syntax
  $a class ( VERINA78TwoSum A B ) $.
verina78-precondition-syntax
  $a wff ( VERINA78Pre A B ) $.
verina78-postcondition-syntax
  $a wff ( VERINA78Post A B C ) $.

verina78-get-bang-definition $a |- (
  VERINA78GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verina78-nat-sub-definition $a |- (
  VERINA78NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

${
  $d r A B C $.

  verina78-pair-rank-definition $a |- (
    VERINA78PairRank A B C
  ) = (
    (
      sum_ r e. ( 0 ..^ B )
        (
          VERINA78NatSub
            ( # ` A )
            ( r + 1 )
        )
    )
    +
    (
      VERINA78NatSub
        C
        ( B + 1 )
    )
  ) $.
$}

${
  $d i j r A B $.

  verina78-pairwise-sums-graph-definition $a |- (
    VERINA78PairwiseSumsGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      (
        # ` B
      ) = (
        sum_ r e. ( 0 ..^ ( # ` A ) )
          (
            VERINA78NatSub
              ( # ` A )
              ( r + 1 )
          )
      )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( ( i + 1 ) ..^ ( # ` A ) )
          (
            B ` ( VERINA78PairRank A i j )
          ) = (
            ( A ` i ) + ( A ` j )
          )
    )
  ) $.
$}

${
  $d y A $.

  verina78-pairwise-sums-definition $a |- (
    VERINA78PairwiseSums A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA78PairwiseSumsGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina78-count-definition $a |- (
    VERINA78Count A B
  ) = (
    # ` {
      k e. ( 0 ..^ ( # ` B ) )
      |
      ( B ` k ) = A
    }
  ) $.
$}

verina78-none-definition $a |- VERINA78None = (/) $.

verina78-some-definition $a |- (
  VERINA78Some A
) = <. 1 , A >. $.

${
  $d x y $.

  verina78-option-nat-definition $a |- VERINA78OptionNat =
    { x |
      (
        x = VERINA78None
        \/
        E. y e. NN0 x = ( VERINA78Some y )
      )
    } $.
$}

${
  $d k A B C $.

  verina78-drop-graph-definition $a |- (
    VERINA78DropGraph A B C
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
        VERINA78NatSub
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

  verina78-drop-definition $a |- (
    VERINA78Drop A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA78DropGraph A B y )
  ) $.
$}

${
  $d k m A B C D E F $.

  verina78-find-complement-aux-graph-definition $a |- (
    VERINA78FindComplementAuxGraph A B C D E F
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
          C e. NN0
          /\
          D e. ZZ
        )
      )
      /\
      (
        E e. NN0
        /\
        F e. VERINA78OptionNat
      )
    )
    /\
    (
      E. k e. ( 0 ..^ ( # ` A ) )
        (
          (
            D + ( A ` k )
          ) = B
          /\
          (
            F = (
              VERINA78Some
                ( ( ( C + E ) + k ) + 1 )
            )
            /\
            A. m e. ( 0 ..^ k )
              (
                D + ( A ` m )
              ) =/= B
          )
        )
      \/
      (
        -.
        E. k e. ( 0 ..^ ( # ` A ) )
          (
            D + ( A ` k )
          ) = B
        /\
        F = VERINA78None
      )
    )
  ) $.
$}

${
  $d o A B C D $.

  verina78-find-complement-definition $a |- (
    VERINA78FindComplement A B C D
  ) = (
    iota_ o e. VERINA78OptionNat
      (
        VERINA78FindComplementAuxGraph
          A B C D 0 o
      )
  ) $.
$}

verina78-pair-nat-definition $a |- VERINA78PairNat = (
  NN0 X. NN0
) $.

${
  $d j k m A B C D $.

  verina78-two-sum-aux-graph-definition $a |- (
    VERINA78TwoSumAuxGraph A B C D
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
      D e. VERINA78PairNat
    )
    /\
    (
      E. k e. ( 0 ..^ ( # ` A ) )
        E. j e. NN0
          (
            (
              VERINA78FindComplement
                ( VERINA78Drop A ( k + 1 ) )
                B
                ( C + k )
                ( A ` k )
            ) = (
              VERINA78Some j
            )
            /\
            (
              D = <. ( C + k ) , j >.
              /\
              A. m e. ( 0 ..^ k )
                (
                  VERINA78FindComplement
                    ( VERINA78Drop A ( m + 1 ) )
                    B
                    ( C + m )
                    ( A ` m )
                ) = VERINA78None
            )
          )
      \/
      (
        (
          A. m e. ( 0 ..^ ( # ` A ) )
            (
              VERINA78FindComplement
                ( VERINA78Drop A ( m + 1 ) )
                B
                ( C + m )
                ( A ` m )
            ) = VERINA78None
        )
        /\
        D = <. 0 , 0 >.
      )
    )
  ) $.
$}

${
  $d p A B C $.

  verina78-two-sum-aux-definition $a |- (
    VERINA78TwoSumAux A B C
  ) = (
    iota_ p e. VERINA78PairNat
      ( VERINA78TwoSumAuxGraph A B C p )
  ) $.
$}

verina78-two-sum-definition $a |- (
  VERINA78TwoSum A B
) = (
  VERINA78TwoSumAux A B 0
) $.

verina78-precondition-definition $a |- (
  VERINA78Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  (
    1 < ( # ` A )
    /\
    (
      VERINA78Count
        B
        ( VERINA78PairwiseSums A )
    ) = 1
  )
) $.

verina78-postcondition-definition $a |- (
  VERINA78Post A B C
) <-> (
  (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    C e. VERINA78PairNat
  )
  /\
  (
    (
      1st ` C
    ) < (
      2nd ` C
    )
    /\
    (
      (
        1st ` C
      ) < (
        # ` A
      )
      /\
      (
        (
          2nd ` C
        ) < (
          # ` A
        )
        /\
        (
          (
            VERINA78GetBang
              A
              ( 1st ` C )
          )
          +
          (
            VERINA78GetBang
              A
              ( 2nd ` C )
          )
        ) = B
      )
    )
  )
) $.

verina-advanced-78-two-sum $a |- A. w e. Word ZZ
  A. z e. ZZ
    (
      ( VERINA78Pre w z )
      ->
      (
        VERINA78Post
          w
          z
          ( VERINA78TwoSum w z )
      )
    )
$.
