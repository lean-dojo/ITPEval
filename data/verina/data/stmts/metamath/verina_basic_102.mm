$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_102 (verina__metamath__verina_basic_102), catalog title twoSum:
  the exact nested array search returns the lexicographically first increasing
  pair of natural indices whose integer entries sum to the target under the
  source existence precondition. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINAB102GetBang reproduces Lean Array.get! on integer arrays, including
  its default value zero outside the array. VERINAB102NatSub is Lean's
  truncated natural subtraction. VERINAB102None and VERINAB102Some provide
  a disjoint tagged encoding of Option (Nat x Nat).

  VERINAB102InnerGraph is the exact local inner recursion. Starting at j, it
  returns the fixed outer index paired with the first later index whose two
  entries sum to the target, or none exactly when the remaining scan has no
  match. VERINAB102OuterGraph is the exact local outer recursion. It tests
  every i satisfying i < nums.size - 1 in increasing order and returns the
  first successful inner result, or none when all such scans fail. Their iota
  definitions select the unique computed options. VERINAB102TwoSum invokes
  outer at zero and reproduces the source panic branch by the inhabited
  default pair <. 0 , 0 >.; the precondition makes that branch unreachable.
  Thus the executable result is fixed independently of the postcondition.

  VERINAB102PairwiseNoSum is exactly the finite-index meaning of
  List.Pairwise (fun a b => a + b != target), and VERINAB102Pre preserves the
  size and pair-existence precondition. In VERINAB102Post, the first finite
  universal clause is equivalent to the source take/zipIdx/drop/all clause:
  no pair with first index below i is valid. Under the preceding i < j and
  j < nums.size bounds, the second finite universal clause is exactly the
  source drop/take/all clause over indices strictly between i and j.

  The proof-valued precondition argument has no computational effect, and the
  postcondition does not inspect it, so it is represented by the antecedent
  of the final correctness assertion. Every earlier $a is syntax or a
  faithful definition required by this rendering, and this database has no
  $p declaration.
$)

$c
  VERINAB102GetBang VERINAB102NatSub
  VERINAB102None VERINAB102Some
  VERINAB102PairNat VERINAB102OptionPair
  VERINAB102PairwiseNoSum
  VERINAB102InnerGraph VERINAB102Inner
  VERINAB102OuterGraph VERINAB102Outer
  VERINAB102TwoSum VERINAB102Pre VERINAB102Post
$.

verinab102-get-bang-syntax
  $a class ( VERINAB102GetBang A B ) $.
verinab102-nat-sub-syntax
  $a class ( VERINAB102NatSub A B ) $.
verinab102-none-syntax
  $a class VERINAB102None $.
verinab102-some-syntax
  $a class ( VERINAB102Some A ) $.
verinab102-pair-nat-syntax
  $a class VERINAB102PairNat $.
verinab102-option-pair-syntax
  $a class VERINAB102OptionPair $.
verinab102-pairwise-no-sum-syntax
  $a wff ( VERINAB102PairwiseNoSum A B ) $.
verinab102-inner-graph-syntax
  $a wff ( VERINAB102InnerGraph A B C D E ) $.
verinab102-inner-syntax
  $a class ( VERINAB102Inner A B C D ) $.
verinab102-outer-graph-syntax
  $a wff ( VERINAB102OuterGraph A B C D ) $.
verinab102-outer-syntax
  $a class ( VERINAB102Outer A B C ) $.
verinab102-two-sum-syntax
  $a class ( VERINAB102TwoSum A B ) $.
verinab102-precondition-syntax
  $a wff ( VERINAB102Pre A B ) $.
verinab102-postcondition-syntax
  $a wff ( VERINAB102Post A B C ) $.

verinab102-get-bang-definition $a |- (
  VERINAB102GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab102-nat-sub-definition $a |- (
  VERINAB102NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab102-none-definition $a |- VERINAB102None = (/) $.

verinab102-some-definition $a |- (
  VERINAB102Some A
) = <. 1 , A >. $.

verinab102-pair-nat-definition $a |- VERINAB102PairNat = (
  NN0 X. NN0
) $.

${
  $d p x $.

  verinab102-option-pair-definition $a |- VERINAB102OptionPair =
    { x |
      (
        x = VERINAB102None
        \/
        E. p e. VERINAB102PairNat x = ( VERINAB102Some p )
      )
    } $.
$}

${
  $d i j A B $.

  verinab102-pairwise-no-sum-definition $a |- (
    VERINAB102PairwiseNoSum A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( ( i + 1 ) ..^ ( # ` A ) )
        (
          ( VERINAB102GetBang A i )
          +
          ( VERINAB102GetBang A j )
        ) =/= B
  ) $.
$}

${
  $d k m A B C D E $.

  verinab102-inner-graph-definition $a |- (
    VERINAB102InnerGraph A B C D E
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
          D e. NN0
        )
      )
      /\
      E e. VERINAB102OptionPair
    )
    /\
    (
      E. k e. ( D ..^ ( # ` A ) )
        (
          (
            ( VERINAB102GetBang A C )
            +
            ( VERINAB102GetBang A k )
          ) = B
          /\
          (
            E = (
              VERINAB102Some <. C , k >.
            )
            /\
            A. m e. ( D ..^ k )
              (
                ( VERINAB102GetBang A C )
                +
                ( VERINAB102GetBang A m )
              ) =/= B
          )
        )
      \/
      (
        -.
        E. k e. ( D ..^ ( # ` A ) )
          (
            ( VERINAB102GetBang A C )
            +
            ( VERINAB102GetBang A k )
          ) = B
        /\
        E = VERINAB102None
      )
    )
  ) $.
$}

${
  $d o A B C D $.

  verinab102-inner-definition $a |- (
    VERINAB102Inner A B C D
  ) = (
    iota_ o e. VERINAB102OptionPair
      ( VERINAB102InnerGraph A B C D o )
  ) $.
$}

${
  $d j k m A B C D $.

  verinab102-outer-graph-definition $a |- (
    VERINAB102OuterGraph A B C D
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
      D e. VERINAB102OptionPair
    )
    /\
    (
      E. k e. (
        C ..^ (
          VERINAB102NatSub ( # ` A ) 1
        )
      )
        E. j e. NN0
          (
            (
              VERINAB102Inner
                A
                B
                k
                ( k + 1 )
            ) = (
              VERINAB102Some <. k , j >.
            )
            /\
            (
              D = (
                VERINAB102Some <. k , j >.
              )
              /\
              A. m e. ( C ..^ k )
                (
                  VERINAB102Inner
                    A
                    B
                    m
                    ( m + 1 )
                ) = VERINAB102None
            )
          )
      \/
      (
        (
          A. m e. (
            C ..^ (
              VERINAB102NatSub ( # ` A ) 1
            )
          )
            (
              VERINAB102Inner
                A
                B
                m
                ( m + 1 )
            ) = VERINAB102None
        )
        /\
        D = VERINAB102None
      )
    )
  ) $.
$}

${
  $d o A B C $.

  verinab102-outer-definition $a |- (
    VERINAB102Outer A B C
  ) = (
    iota_ o e. VERINAB102OptionPair
      ( VERINAB102OuterGraph A B C o )
  ) $.
$}

${
  $d p A B $.

  verinab102-two-sum-definition $a |- (
    VERINAB102TwoSum A B
  ) = if (
    ( VERINAB102Outer A B 0 ) = VERINAB102None ,
    <. 0 , 0 >. ,
    iota_ p e. VERINAB102PairNat
      (
        ( VERINAB102Outer A B 0 )
        =
        ( VERINAB102Some p )
      )
  ) $.
$}

verinab102-precondition-definition $a |- (
  VERINAB102Pre A B
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
    -. ( VERINAB102PairwiseNoSum A B )
  )
) $.

${
  $d i j m n A B C $.

  verinab102-postcondition-definition $a |- (
    VERINAB102Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. VERINAB102PairNat
    )
    /\
    E. i e. NN0 E. j e. NN0
      (
        C = <. i , j >.
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
              ( VERINAB102GetBang A i )
              +
              ( VERINAB102GetBang A j )
            ) = B
            /\
            (
              A. m e. ( 0 ..^ i )
                A. n e. ( ( m + 1 ) ..^ ( # ` A ) )
                  (
                    ( VERINAB102GetBang A m )
                    +
                    ( VERINAB102GetBang A n )
                  ) =/= B
              /\
              A. n e. ( ( i + 1 ) ..^ j )
                (
                  ( VERINAB102GetBang A i )
                  +
                  ( VERINAB102GetBang A n )
                ) =/= B
            )
          )
        )
      )
  ) $.
$}

verina-basic-102-two-sum $a |- A. w e. Word ZZ
  A. z e. ZZ
    (
      ( VERINAB102Pre w z )
      ->
      (
        VERINAB102Post
          w
          z
          ( VERINAB102TwoSum w z )
      )
    )
$.
