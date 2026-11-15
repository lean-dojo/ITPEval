$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_62 (verina__metamath__verina_advanced_62), catalog title
  rain: the exact two-pointer program computes trapped rainwater for an
  arbitrary finite list of nonnegative integer heights, with the independent
  per-position maximum-and-sum correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer lists. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA62GetBang reproduces Lean's zero-default list indexing. VERINA62NatSub
  is truncated natural subtraction, while VERINA62IntMin and VERINA62IntMax
  are integer minimum and maximum.

  VERINA62State stores, in order, left, right, leftMax, rightMax, and water.
  VERINA62Step is exactly one nonterminal branch of the source aux recursion:
  it processes the left entry when that height is at most the right entry,
  and otherwise processes the right entry. VERINA62AuxGraph records the
  complete deterministic trace until left is at least right, and returns the
  terminal water component. VERINA62Rain preserves the source branch returning
  zero below length three and otherwise initializes aux at both endpoints.

  VERINA62MaxLeftGraph is the exact ml recursion from zero through index i.
  VERINA62MaxRightGraph is the exact mr recursion from index i through the end.
  VERINA62WaterAt applies the source max-zero formula, and
  VERINA62SumWaterGraph is the exact sum_water recursion from index zero and
  accumulator zero. These traces define the postcondition independently of
  the two-pointer implementation.

  VERINA62Pre is precisely the source List.all nonnegativity requirement on a
  typed List Int input. VERINA62Post preserves nonnegativity of the result and
  both branches of the source postcondition. The proof-valued precondition
  argument is computationally and propositionally unused and is represented
  by the explicit antecedent of the final correctness assertion. Every
  earlier $a is syntax or a faithful definition, and this database has no
  $p declaration.
$)

$c
  VERINA62GetBang VERINA62NatSub
  VERINA62IntMin VERINA62IntMax
  VERINA62State VERINA62Step
  VERINA62AuxGraph VERINA62Aux
  VERINA62Pre VERINA62Rain
  VERINA62MaxLeftGraph VERINA62MaxLeftAt
  VERINA62MaxRightGraph VERINA62MaxRightAt
  VERINA62WaterAt
  VERINA62SumWaterGraph VERINA62SumWater
  VERINA62Post
$.

verina62-get-bang-syntax
  $a class ( VERINA62GetBang A B ) $.
verina62-nat-sub-syntax
  $a class ( VERINA62NatSub A B ) $.
verina62-int-min-syntax
  $a class ( VERINA62IntMin A B ) $.
verina62-int-max-syntax
  $a class ( VERINA62IntMax A B ) $.
verina62-state-syntax
  $a class VERINA62State $.
verina62-step-syntax
  $a class ( VERINA62Step A B ) $.
verina62-aux-graph-syntax
  $a wff ( VERINA62AuxGraph A B C ) $.
verina62-aux-syntax
  $a class ( VERINA62Aux A B ) $.
verina62-precondition-syntax
  $a wff ( VERINA62Pre A ) $.
verina62-rain-syntax
  $a class ( VERINA62Rain A ) $.
verina62-max-left-graph-syntax
  $a wff ( VERINA62MaxLeftGraph A B C ) $.
verina62-max-left-at-syntax
  $a class ( VERINA62MaxLeftAt A B ) $.
verina62-max-right-graph-syntax
  $a wff ( VERINA62MaxRightGraph A B C ) $.
verina62-max-right-at-syntax
  $a class ( VERINA62MaxRightAt A B ) $.
verina62-water-at-syntax
  $a class ( VERINA62WaterAt A B ) $.
verina62-sum-water-graph-syntax
  $a wff ( VERINA62SumWaterGraph A B ) $.
verina62-sum-water-syntax
  $a class ( VERINA62SumWater A ) $.
verina62-postcondition-syntax
  $a wff ( VERINA62Post A B ) $.

verina62-get-bang-definition $a |- (
  VERINA62GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verina62-nat-sub-definition $a |- (
  VERINA62NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verina62-int-min-definition $a |- (
  VERINA62IntMin A B
) = if (
  A < B ,
  A ,
  B
) $.

verina62-int-max-definition $a |- (
  VERINA62IntMax A B
) = if (
  A < B ,
  B ,
  A
) $.

verina62-state-definition $a |- VERINA62State = (
  NN0 X. ( NN0 X. ( ZZ X. ( ZZ X. ZZ ) ) )
) $.

verina62-step-definition $a |- (
  VERINA62Step A B
) = if (
  (
    VERINA62GetBang
      A
      ( 1st ` B )
  ) <_ (
    VERINA62GetBang
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
          VERINA62IntMax
            ( 1st ` ( 2nd ` ( 2nd ` B ) ) )
            (
              VERINA62GetBang
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
              VERINA62IntMax
                0
                (
                  ( 1st ` ( 2nd ` ( 2nd ` B ) ) )
                  -
                  (
                    VERINA62GetBang
                      A
                      ( 1st ` B )
                  )
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
        VERINA62NatSub
          ( 1st ` ( 2nd ` B ) )
          1
      )
      ,
      <.
        ( 1st ` ( 2nd ` ( 2nd ` B ) ) )
        ,
        <.
          (
            VERINA62IntMax
              ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` B ) ) ) )
              (
                VERINA62GetBang
                  A
                  ( 1st ` ( 2nd ` B ) )
              )
          )
          ,
          (
            ( 2nd ` ( 2nd ` ( 2nd ` ( 2nd ` B ) ) ) )
            +
            (
              VERINA62IntMax
                0
                (
                  ( 1st ` ( 2nd ` ( 2nd ` ( 2nd ` B ) ) ) )
                  -
                  (
                    VERINA62GetBang
                      A
                      ( 1st ` ( 2nd ` B ) )
                  )
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

  verina62-aux-graph-definition $a |- (
    VERINA62AuxGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. VERINA62State
      )
      /\
      C e. ZZ
    )
    /\
    E. k e. NN0 E. t e. Word VERINA62State
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
                VERINA62Step A ( t ` i )
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

  verina62-aux-definition $a |- (
    VERINA62Aux A B
  ) = (
    iota_ y e. ZZ
      ( VERINA62AuxGraph A B y )
  ) $.
$}

${
  $d i A $.

  verina62-precondition-definition $a |- (
    VERINA62Pre A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      0 <_ ( A ` i )
  ) $.
$}

verina62-rain-definition $a |- (
  VERINA62Rain A
) = if (
  ( # ` A ) < 3 ,
  0 ,
  (
    VERINA62Aux
      A
      <.
        0
        ,
        <.
          ( VERINA62NatSub ( # ` A ) 1 )
          ,
          <.
            ( VERINA62GetBang A 0 )
            ,
            <.
              (
                VERINA62GetBang
                  A
                  ( VERINA62NatSub ( # ` A ) 1 )
              )
              ,
              0
            >.
          >.
        >.
      >.
  )
) $.

${
  $d k m A B C $.

  verina62-max-left-graph-definition $a |- (
    VERINA62MaxLeftGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. ZZ
    )
    /\
    E. m e. Word ZZ
      (
        (
          ( # ` m ) = ( B + 2 )
          /\
          ( m ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( B + 1 ) )
            (
              m ` ( k + 1 )
            ) = (
              VERINA62IntMax
                ( m ` k )
                ( VERINA62GetBang A k )
            )
          /\
          C = ( m ` ( B + 1 ) )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verina62-max-left-at-definition $a |- (
    VERINA62MaxLeftAt A B
  ) = (
    iota_ y e. ZZ
      ( VERINA62MaxLeftGraph A B y )
  ) $.
$}

${
  $d d k m A B C $.

  verina62-max-right-graph-definition $a |- (
    VERINA62MaxRightGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. ZZ
    )
    /\
    E. d e. NN0 E. m e. Word ZZ
      (
        (
          d = ( VERINA62NatSub ( # ` A ) B )
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
              VERINA62IntMax
                ( m ` k )
                (
                  VERINA62GetBang
                    A
                    ( B + k )
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

  verina62-max-right-at-definition $a |- (
    VERINA62MaxRightAt A B
  ) = (
    iota_ y e. ZZ
      ( VERINA62MaxRightGraph A B y )
  ) $.
$}

verina62-water-at-definition $a |- (
  VERINA62WaterAt A B
) = (
  VERINA62IntMax
    0
    (
      (
        VERINA62IntMin
          ( VERINA62MaxLeftAt A B )
          ( VERINA62MaxRightAt A B )
      )
      -
      ( VERINA62GetBang A B )
    )
) $.

${
  $d i s A B $.

  verina62-sum-water-graph-definition $a |- (
    VERINA62SumWaterGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    E. s e. Word ZZ
      (
        (
          ( # ` s ) = ( ( # ` A ) + 1 )
          /\
          ( s ` 0 ) = 0
        )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              s ` ( i + 1 )
            ) = (
              ( s ` i )
              +
              ( VERINA62WaterAt A i )
            )
          /\
          B = ( s ` ( # ` A ) )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina62-sum-water-definition $a |- (
    VERINA62SumWater A
  ) = (
    iota_ y e. ZZ
      ( VERINA62SumWaterGraph A y )
  ) $.
$}

verina62-postcondition-definition $a |- (
  VERINA62Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  (
    0 <_ B
    /\
    (
      (
        ( # ` A ) < 3
        ->
        B = 0
      )
      /\
      (
        -. ( ( # ` A ) < 3 )
        ->
        B = ( VERINA62SumWater A )
      )
    )
  )
) $.

verina-advanced-62-rain $a |- A. w e. Word ZZ
  (
    ( VERINA62Pre w )
    ->
    (
      VERINA62Post
        w
        ( VERINA62Rain w )
    )
  )
$.
