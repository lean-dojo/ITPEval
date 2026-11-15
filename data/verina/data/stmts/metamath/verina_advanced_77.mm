$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_77 (verina__metamath__verina_advanced_77), catalog title
  trapRainWater: the exact recursive two-pointer program computes trapped
  rainwater for an arbitrary finite natural-number elevation list, with the
  independent prefix/suffix-maximum sum correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA77GetBang reproduces Lean's zero-default List.get! indexing.
  VERINA77NatMin and VERINA77NatMax are natural minimum and maximum, and
  VERINA77NatSub is Lean's truncated natural subtraction.

  VERINA77State stores, in order, left, right, leftMax, rightMax, and water.
  VERINA77Step is exactly one nonterminal trapLoop branch. It compares the
  current endpoint heights before updating either maximum; the left branch
  is taken exactly for a strict height inequality, and the right branch
  otherwise. Its maximum and truncated-subtraction expressions reproduce
  both source inner conditionals, including their equality cases.
  VERINA77TrapLoopGraph records the complete deterministic trace from an
  arbitrary typed helper state until left is at least right and returns the
  terminal water component. VERINA77TrapLoop selects that unique result.
  VERINA77TrapRainWater invokes it at left zero, truncated length-minus-one
  on the right, and zero maxima and water, so the implementation is fixed
  independently of the postcondition.

  VERINA77PrefixMaxGraph is exactly
  (height.take (i + 1)).foldl Nat.max 0, including clipping take at the list
  length. VERINA77SuffixMaxGraph is exactly
  (height.drop i).foldl Nat.max 0, including an empty suffix for an index at
  or beyond the list length. VERINA77WaterAt applies the source natural
  minimum and truncated subtraction. VERINA77ExpectedWater is the finite
  natural sum over the complete List.range height.length and is definitionally
  equivalent to mapping VERINA77WaterAt and folding natural addition from
  zero.

  VERINA77Pre is the source True precondition together with the List Nat
  input type. VERINA77Post preserves both source conjuncts: result minus the
  expected fold sum is zero under truncated subtraction, and the expected
  sum is at most result. The proof-valued precondition arguments are
  computationally and propositionally unused and are represented by the
  explicit antecedent of the final correctness assertion. Every earlier $a
  is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINA77GetBang
  VERINA77NatMin VERINA77NatMax VERINA77NatSub
  VERINA77State VERINA77Step
  VERINA77TrapLoopGraph VERINA77TrapLoop
  VERINA77Pre VERINA77TrapRainWater
  VERINA77PrefixMaxGraph VERINA77PrefixMax
  VERINA77SuffixMaxGraph VERINA77SuffixMax
  VERINA77WaterAt VERINA77ExpectedWater
  VERINA77Post
$.

verina77-get-bang-syntax
  $a class ( VERINA77GetBang A B ) $.
verina77-nat-min-syntax
  $a class ( VERINA77NatMin A B ) $.
verina77-nat-max-syntax
  $a class ( VERINA77NatMax A B ) $.
verina77-nat-sub-syntax
  $a class ( VERINA77NatSub A B ) $.
verina77-state-syntax
  $a class VERINA77State $.
verina77-step-syntax
  $a class ( VERINA77Step A B ) $.
verina77-trap-loop-graph-syntax
  $a wff ( VERINA77TrapLoopGraph A B C ) $.
verina77-trap-loop-syntax
  $a class ( VERINA77TrapLoop A B ) $.
verina77-precondition-syntax
  $a wff ( VERINA77Pre A ) $.
verina77-trap-rain-water-syntax
  $a class ( VERINA77TrapRainWater A ) $.
verina77-prefix-max-graph-syntax
  $a wff ( VERINA77PrefixMaxGraph A B C ) $.
verina77-prefix-max-syntax
  $a class ( VERINA77PrefixMax A B ) $.
verina77-suffix-max-graph-syntax
  $a wff ( VERINA77SuffixMaxGraph A B C ) $.
verina77-suffix-max-syntax
  $a class ( VERINA77SuffixMax A B ) $.
verina77-water-at-syntax
  $a class ( VERINA77WaterAt A B ) $.
verina77-expected-water-syntax
  $a class ( VERINA77ExpectedWater A ) $.
verina77-postcondition-syntax
  $a wff ( VERINA77Post A B ) $.

verina77-get-bang-definition $a |- (
  VERINA77GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verina77-nat-min-definition $a |- (
  VERINA77NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

verina77-nat-max-definition $a |- (
  VERINA77NatMax A B
) = if (
  A < B ,
  B ,
  A
) $.

verina77-nat-sub-definition $a |- (
  VERINA77NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verina77-state-definition $a |- VERINA77State = (
  NN0 X. ( NN0 X. ( NN0 X. ( NN0 X. NN0 ) ) )
) $.

verina77-step-definition $a |- (
  VERINA77Step A B
) = if (
  (
    VERINA77GetBang
      A
      ( 1st ` B )
  ) < (
    VERINA77GetBang
      A
      ( 1st ` ( 2nd ` B ) )
  )
  ,
  <.
    ( ( 1st ` B ) + 1 )
    ,
    <.
      ( 1st ` ( 2nd ` B ) )
      ,
      <.
        (
          VERINA77NatMax
            ( 1st ` ( 2nd ` ( 2nd ` B ) ) )
            (
              VERINA77GetBang
                A
                ( 1st ` B )
            )
        )
        ,
        <.
          ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` B ) ) ) )
          ,
          (
            ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` B ) ) ) )
            +
            (
              VERINA77NatSub
                ( 1st ` ( 2nd ` ( 2nd ` B ) ) )
                (
                  VERINA77GetBang
                    A
                    ( 1st ` B )
                )
            )
          )
        >.
      >.
    >.
  >.
  ,
  <.
    ( 1st ` B )
    ,
    <.
      (
        VERINA77NatSub
          ( 1st ` ( 2nd ` B ) )
          1
      )
      ,
      <.
        ( 1st ` ( 2nd ` ( 2nd ` B ) ) )
        ,
        <.
          (
            VERINA77NatMax
              ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` B ) ) ) )
              (
                VERINA77GetBang
                  A
                  ( 1st ` ( 2nd ` B ) )
              )
          )
          ,
          (
            ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` B ) ) ) )
            +
            (
              VERINA77NatSub
                ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` B ) ) ) )
                (
                  VERINA77GetBang
                    A
                    ( 1st ` ( 2nd ` B ) )
                )
            )
          )
        >.
      >.
    >.
  >.
) $.

${
  $d i k t A B C $.

  verina77-trap-loop-graph-definition $a |- (
    VERINA77TrapLoopGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. VERINA77State
      )
      /\
      C e. NN0
    )
    /\
    E. k e. NN0 E. t e. Word VERINA77State
      (
        (
          ( # ` t ) = ( k + 1 )
          /\
          ( t ` 0 ) = B
        )
        /\
        (
          A. i e. ( 0 ..^ k )
            (
              (
                1st ` ( t ` i )
              ) < (
                1st ` ( 2nd ` ( t ` i ) )
              )
              /\
              (
                t ` ( i + 1 )
              ) = (
                VERINA77Step A ( t ` i )
              )
            )
          /\
          (
            (
              1st ` ( 2nd ` ( t ` k ) )
            ) <_ (
              1st ` ( t ` k )
            )
            /\
            C = (
              2nd ` (
                2nd ` (
                  2nd ` (
                    2nd ` ( t ` k )
                  )
                )
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina77-trap-loop-definition $a |- (
    VERINA77TrapLoop A B
  ) = (
    iota_ y e. NN0
      ( VERINA77TrapLoopGraph A B y )
  ) $.
$}

verina77-precondition-definition $a |- (
  VERINA77Pre A
) <-> (
  A e. Word NN0
) $.

verina77-trap-rain-water-definition $a |- (
  VERINA77TrapRainWater A
) = (
  VERINA77TrapLoop
    A
    <.
      0
      ,
      <.
        ( VERINA77NatSub ( # ` A ) 1 )
        ,
        <.
          0
          ,
          <.
            0
            ,
            0
          >.
        >.
      >.
    >.
) $.

${
  $d d k m A B C $.

  verina77-prefix-max-graph-definition $a |- (
    VERINA77PrefixMaxGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. NN0
    )
    /\
    E. d e. NN0 E. m e. Word NN0
      (
        (
          d = (
            VERINA77NatMin
              ( B + 1 )
              ( # ` A )
          )
          /\
          (
            ( # ` m ) = ( d + 1 )
            /\
            ( m ` 0 ) = 0
          )
        )
        /\
        (
          A. k e. ( 0 ..^ d )
            (
              m ` ( k + 1 )
            ) = (
              VERINA77NatMax
                ( m ` k )
                ( VERINA77GetBang A k )
            )
          /\
          C = ( m ` d )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina77-prefix-max-definition $a |- (
    VERINA77PrefixMax A B
  ) = (
    iota_ y e. NN0
      ( VERINA77PrefixMaxGraph A B y )
  ) $.
$}

${
  $d d k m s A B C $.

  verina77-suffix-max-graph-definition $a |- (
    VERINA77SuffixMaxGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. NN0
      )
      /\
      C e. NN0
    )
    /\
    E. s e. NN0 E. d e. NN0 E. m e. Word NN0
      (
        (
          s = ( VERINA77NatMin B ( # ` A ) )
          /\
          (
            d = ( VERINA77NatSub ( # ` A ) s )
            /\
            (
              ( # ` m ) = ( d + 1 )
              /\
              ( m ` 0 ) = 0
            )
          )
        )
        /\
        (
          A. k e. ( 0 ..^ d )
            (
              m ` ( k + 1 )
            ) = (
              VERINA77NatMax
                ( m ` k )
                (
                  VERINA77GetBang
                    A
                    ( s + k )
                )
            )
          /\
          C = ( m ` d )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina77-suffix-max-definition $a |- (
    VERINA77SuffixMax A B
  ) = (
    iota_ y e. NN0
      ( VERINA77SuffixMaxGraph A B y )
  ) $.
$}

verina77-water-at-definition $a |- (
  VERINA77WaterAt A B
) = (
  VERINA77NatSub
    (
      VERINA77NatMin
        ( VERINA77PrefixMax A B )
        ( VERINA77SuffixMax A B )
    )
    ( VERINA77GetBang A B )
) $.

${
  $d i A $.

  verina77-expected-water-definition $a |- (
    VERINA77ExpectedWater A
  ) = (
    sum_ i e. ( 0 ..^ ( # ` A ) )
      ( VERINA77WaterAt A i )
  ) $.
$}

verina77-postcondition-definition $a |- (
  VERINA77Post A B
) <-> (
  (
    A e. Word NN0
    /\
    B e. NN0
  )
  /\
  (
    (
      VERINA77NatSub
        B
        ( VERINA77ExpectedWater A )
    ) = 0
    /\
    ( VERINA77ExpectedWater A ) <_ B
  )
) $.

verina-advanced-77-trap-rain-water $a |- A. w e. Word NN0
  (
    ( VERINA77Pre w )
    ->
    (
      VERINA77Post
        w
        ( VERINA77TrapRainWater w )
    )
  )
$.
