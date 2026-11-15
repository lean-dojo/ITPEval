$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_25
  (verina__metamath__verina_basic_25), catalog title sumAndAverage: the exact
  executable range summation returns its integer total and IEEE-754 binary64
  average under the positive less-than-2^53 precondition, together with the
  closed-form correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0, ZZ, and RR are the full natural, integer, and real domains.
  VERINAB25Float64 is the full set of 64-bit IEEE encodings, not a rational
  replacement for Float. VERINAB25PosFinite identifies positive-sign finite
  encodings. VERINAB25FloatValue gives their exact real values, including
  subnormals, and VERINAB25RoundGraph is round-to-nearest, ties-to-even.
  Consequently VERINAB25NatToFloat and VERINAB25FloatDiv are the exact
  binary64 operations on every positive finite value reached by this program.

  VERINAB25FloatBEq is Lean Float BEq on all 64-bit encodings: NaN compares
  unequal to every value, the two signed zero encodings compare equal, and all
  other values compare exactly when their encodings agree.

  VERINAB25SumGraph records every accumulator of List.range (n + 1).sum:
  it starts at zero and adds k + 1 at transition k. VERINAB25Sum selects its
  unique final value. VERINAB25Program preserves the source conditional and,
  on the positive branch, returns that sum together with the rounded quotient
  of the separately rounded natural operands. The proof-valued precondition
  argument has no computational effect and is represented by the explicit
  antecedent in the final assertion.

  VERINAB25Pre is exactly 0 < n < 2^53. VERINAB25Post preserves both source
  implications, Int equality, Float BEq, and natural division by two in the
  triangular expression. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c
  VERINAB25Float64 VERINAB25PosFinite
  VERINAB25FloatValueGraph VERINAB25FloatValue
  VERINAB25RoundGraph VERINAB25Round
  VERINAB25NatToFloat VERINAB25FloatDiv
  VERINAB25IsNaN VERINAB25IsZero VERINAB25FloatBEq
  VERINAB25PairBEq
  VERINAB25SumGraph VERINAB25Sum
  VERINAB25Pre VERINAB25Program VERINAB25Post
$.

verinab25-float64-syntax
  $a class VERINAB25Float64 $.
verinab25-pos-finite-syntax
  $a class VERINAB25PosFinite $.
verinab25-float-value-graph-syntax
  $a wff ( VERINAB25FloatValueGraph A B ) $.
verinab25-float-value-syntax
  $a class ( VERINAB25FloatValue A ) $.
verinab25-round-graph-syntax
  $a wff ( VERINAB25RoundGraph A B ) $.
verinab25-round-syntax
  $a class ( VERINAB25Round A ) $.
verinab25-nat-to-float-syntax
  $a class ( VERINAB25NatToFloat A ) $.
verinab25-float-div-syntax
  $a class ( VERINAB25FloatDiv A B ) $.
verinab25-is-nan-syntax
  $a wff ( VERINAB25IsNaN A ) $.
verinab25-is-zero-syntax
  $a wff ( VERINAB25IsZero A ) $.
verinab25-float-beq-syntax
  $a wff ( VERINAB25FloatBEq A B ) $.
verinab25-pair-beq-syntax
  $a wff ( VERINAB25PairBEq A B ) $.
verinab25-sum-graph-syntax
  $a wff ( VERINAB25SumGraph A B ) $.
verinab25-sum-syntax
  $a class ( VERINAB25Sum A ) $.
verinab25-precondition-syntax
  $a wff ( VERINAB25Pre A ) $.
verinab25-program-syntax
  $a class ( VERINAB25Program A ) $.
verinab25-postcondition-syntax
  $a wff ( VERINAB25Post A B ) $.

verinab25-float64-definition $a |- VERINAB25Float64 =
  ( 0 ..^ ( 2 ^ 6 4 ) ) $.

${
  $d c q f $.

  verinab25-pos-finite-definition $a |- VERINAB25PosFinite =
    { c |
      E. q e. ( 0 ..^ 2 0 4 7 )
        E. f e. ( 0 ..^ ( 2 ^ 5 2 ) )
          c = (
            ( q x. ( 2 ^ 5 2 ) ) + f
          )
    } $.
$}

${
  $d q f A B $.

  verinab25-float-value-graph-definition $a |- (
    VERINAB25FloatValueGraph A B
  ) <-> (
    (
      A e. VERINAB25PosFinite
      /\
      B e. RR
    )
    /\
    E. q e. ( 0 ..^ 2 0 4 7 )
      E. f e. ( 0 ..^ ( 2 ^ 5 2 ) )
        (
          A = (
            ( q x. ( 2 ^ 5 2 ) ) + f
          )
          /\
          B = if (
            q = 0 ,
            ( f / ( 2 ^ 1 0 7 4 ) ) ,
            if (
              q <_ 1 0 7 5 ,
              (
                ( ( 2 ^ 5 2 ) + f )
                /
                ( 2 ^ ( 1 0 7 5 - q ) )
              ) ,
              (
                ( ( 2 ^ 5 2 ) + f )
                x.
                ( 2 ^ ( q - 1 0 7 5 ) )
              )
            )
          )
        )
  ) $.
$}

${
  $d x A $.

  verinab25-float-value-definition $a |- (
    VERINAB25FloatValue A
  ) = (
    iota_ x e. RR
      ( VERINAB25FloatValueGraph A x )
  ) $.
$}

${
  $d d A B $.

  verinab25-round-graph-definition $a |- (
    VERINAB25RoundGraph A B
  ) <-> (
    (
      (
        A e. RR
        /\
        0 <_ A
      )
      /\
      B e. VERINAB25PosFinite
    )
    /\
    (
      A. d e. VERINAB25PosFinite
        (
          ( A - ( VERINAB25FloatValue B ) ) ^ 2
          <_
          ( A - ( VERINAB25FloatValue d ) ) ^ 2
        )
      /\
      A. d e. VERINAB25PosFinite
        (
          (
            (
              ( A - ( VERINAB25FloatValue B ) ) ^ 2
              =
              ( A - ( VERINAB25FloatValue d ) ) ^ 2
            )
            /\
            ( d mod 2 ) = 0
          )
          ->
          ( B mod 2 ) = 0
        )
    )
  ) $.
$}

${
  $d c A $.

  verinab25-round-definition $a |- (
    VERINAB25Round A
  ) = (
    iota_ c e. VERINAB25PosFinite
      ( VERINAB25RoundGraph A c )
  ) $.
$}

verinab25-nat-to-float-definition $a |- (
  VERINAB25NatToFloat A
) = (
  VERINAB25Round A
) $.

verinab25-float-div-definition $a |- (
  VERINAB25FloatDiv A B
) = (
  VERINAB25Round
    (
      ( VERINAB25FloatValue A )
      /
      ( VERINAB25FloatValue B )
    )
) $.

verinab25-is-nan-definition $a |- (
  VERINAB25IsNaN A
) <-> (
  (
    A e. VERINAB25Float64
    /\
    (
      (
        ( |_ ` ( A / ( 2 ^ 5 2 ) ) )
        mod
        ( 2 ^ 1 1 )
      ) = 2 0 4 7
    )
  )
  /\
  ( A mod ( 2 ^ 5 2 ) ) =/= 0
) $.

verinab25-is-zero-definition $a |- (
  VERINAB25IsZero A
) <-> (
  (
    A e. VERINAB25Float64
    /\
    (
      (
        ( |_ ` ( A / ( 2 ^ 5 2 ) ) )
        mod
        ( 2 ^ 1 1 )
      ) = 0
    )
  )
  /\
  ( A mod ( 2 ^ 5 2 ) ) = 0
) $.

verinab25-float-beq-definition $a |- (
  VERINAB25FloatBEq A B
) <-> (
  (
    (
      A e. VERINAB25Float64
      /\
      B e. VERINAB25Float64
    )
    /\
    (
      -. ( VERINAB25IsNaN A )
      /\
      -. ( VERINAB25IsNaN B )
    )
  )
  /\
  (
    A = B
    \/
    (
      ( VERINAB25IsZero A )
      /\
      ( VERINAB25IsZero B )
    )
  )
) $.

verinab25-pair-beq-definition $a |- (
  VERINAB25PairBEq A B
) <-> (
  (
    A e. ( ZZ X. VERINAB25Float64 )
    /\
    B e. ( ZZ X. VERINAB25Float64 )
  )
  /\
  (
    ( 1st ` A ) = ( 1st ` B )
    /\
    (
      VERINAB25FloatBEq
        ( 2nd ` A )
        ( 2nd ` B )
    )
  )
) $.

${
  $d k t A B $.

  verinab25-sum-graph-definition $a |- (
    VERINAB25SumGraph A B
  ) <-> (
    (
      A e. NN0
      /\
      B e. NN0
    )
    /\
    E. t e. Word NN0
      (
        (
          ( # ` t ) = ( A + 1 )
          /\
          ( t ` 0 ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ A )
            (
              ( t ` ( k + 1 ) )
              =
              ( ( t ` k ) + ( k + 1 ) )
            )
          /\
          B = ( t ` A )
        )
      )
  ) $.
$}

${
  $d s A $.

  verinab25-sum-definition $a |- (
    VERINAB25Sum A
  ) = (
    iota_ s e. NN0
      ( VERINAB25SumGraph A s )
  ) $.
$}

verinab25-precondition-definition $a |- (
  VERINAB25Pre A
) <-> (
  (
    A e. NN0
    /\
    0 < A
  )
  /\
  A < ( 2 ^ 5 3 )
) $.

verinab25-program-definition $a |- (
  VERINAB25Program A
) = if (
  A <_ 0 ,
  <. 0 , 0 >. ,
  <.
    ( VERINAB25Sum A )
    ,
    (
      VERINAB25FloatDiv
        ( VERINAB25NatToFloat ( VERINAB25Sum A ) )
        ( VERINAB25NatToFloat A )
    )
  >.
) $.

verinab25-postcondition-definition $a |- (
  VERINAB25Post A B
) <-> (
  (
    A e. NN0
    /\
    B e. ( ZZ X. VERINAB25Float64 )
  )
  /\
  (
    (
      A = 0
      ->
      (
        VERINAB25PairBEq
          B
          <. 0 , 0 >.
      )
    )
    /\
    (
      0 < A
      ->
      (
        (
          ( 1st ` B )
          =
          (
            |_ `
            (
              ( A x. ( A + 1 ) )
              /
              2
            )
          )
        )
        /\
        (
          VERINAB25FloatBEq
            ( 2nd ` B )
            (
              VERINAB25FloatDiv
                (
                  VERINAB25NatToFloat
                    (
                      |_ `
                      (
                        ( A x. ( A + 1 ) )
                        /
                        2
                      )
                    )
                )
                ( VERINAB25NatToFloat A )
            )
        )
      )
    )
  )
) $.

verina-basic-25-sum-and-average $a |- A. n e. NN0
  (
    ( VERINAB25Pre n )
    ->
    (
      VERINAB25Post
        n
        ( VERINAB25Program n )
    )
  )
$.
