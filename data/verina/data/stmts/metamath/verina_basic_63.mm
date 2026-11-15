$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_63
  (verina__metamath__verina_basic_63), catalog title has_close_elements: the
  exact executable nested scan of a finite IEEE-754 binary64 list returns true
  exactly when an earlier/later pair has absolute difference below a valid
  nonnegative threshold, and satisfies its pairwise-separation correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  VERINAB63Float64 is the full set of 64-bit IEEE-754 binary64 encodings,
  rather than a replacement by real or rational numbers. VERINAB63Sign,
  VERINAB63Exponent, and VERINAB63Fraction recover the three encoding fields.
  VERINAB63Finite, VERINAB63IsNaN, and VERINAB63IsInf are the exact IEEE
  classifications. VERINAB63FloatValue gives every finite encoding its exact
  real value, including subnormals and both signed zeros.

  VERINAB63RoundMagnitude is round-to-nearest, ties-to-even on nonnegative
  real magnitudes, with the exact binary64 overflow midpoint selecting
  positive infinity. VERINAB63SignedRound attaches the sign, and
  VERINAB63FloatSub is exact binary64 subtraction for the finite operands used
  by the source program. Its exact-zero case preserves the sole negative-zero
  subtraction case, negative zero minus positive zero. VERINAB63FloatLT and
  VERINAB63FloatLE are IEEE ordered comparisons on every non-NaN encoding,
  including infinities and equality of signed zeros. These definitions
  directly realize the Float behavior described by the source auxiliary
  assumptions instead of adding those facts as premises.

  VERINAB63GetD reproduces List.getD with the positive-zero default.
  VERINAB63AbsDiff is exactly the source helper: it computes a - b, tests that
  rounded result against positive zero, and chooses b - a only on the negative
  branch. VERINAB63Pre preserves the nonnegative non-NaN threshold and the
  requirement that every list entry is finite.

  VERINAB63InnerGraph tabulates the Boolean result of the source inner
  recursion at every index from the outer index down to zero. The state at the
  outer index is false; each preceding state is true exactly when the current
  pair is close, otherwise it is the next state. VERINAB63OuterGraph similarly
  tabulates the outer recursion from the list length down to zero. Thus
  VERINAB63HasCloseElements is the unique result of the exact nested,
  early-exit computation and admits no extra output.

  VERINAB63Pairwise is exactly List.Pairwise of rounded absolute difference
  greater than or equal to the threshold, expressed over every earlier/later
  index pair. VERINAB63Post preserves the source equivalence between a false
  result and that pairwise predicate. The proof-valued precondition arguments
  are computationally and propositionally represented by the explicit
  precondition antecedent in the final correctness assertion. Every earlier
  $a is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB63Float64 VERINAB63Sign VERINAB63Exponent VERINAB63Fraction
  VERINAB63Finite VERINAB63IsNaN VERINAB63IsInf VERINAB63IsZero
  VERINAB63PosFinite VERINAB63PosInf VERINAB63NegInf
  VERINAB63FloatValueGraph VERINAB63FloatValue
  VERINAB63RoundMagnitudeGraph VERINAB63RoundMagnitude
  VERINAB63SignedRound VERINAB63FloatSubGraph VERINAB63FloatSub
  VERINAB63FloatLT VERINAB63FloatLE
  VERINAB63GetD VERINAB63AbsDiff VERINAB63Pre
  VERINAB63InnerGraph VERINAB63Inner
  VERINAB63OuterGraph VERINAB63HasCloseElements
  VERINAB63Pairwise VERINAB63Post
$.

verinab63-float64-syntax
  $a class VERINAB63Float64 $.
verinab63-sign-syntax
  $a class ( VERINAB63Sign A ) $.
verinab63-exponent-syntax
  $a class ( VERINAB63Exponent A ) $.
verinab63-fraction-syntax
  $a class ( VERINAB63Fraction A ) $.
verinab63-finite-syntax
  $a wff ( VERINAB63Finite A ) $.
verinab63-is-nan-syntax
  $a wff ( VERINAB63IsNaN A ) $.
verinab63-is-inf-syntax
  $a wff ( VERINAB63IsInf A ) $.
verinab63-is-zero-syntax
  $a wff ( VERINAB63IsZero A ) $.
verinab63-pos-finite-syntax
  $a class VERINAB63PosFinite $.
verinab63-pos-inf-syntax
  $a class VERINAB63PosInf $.
verinab63-neg-inf-syntax
  $a class VERINAB63NegInf $.
verinab63-float-value-graph-syntax
  $a wff ( VERINAB63FloatValueGraph A B ) $.
verinab63-float-value-syntax
  $a class ( VERINAB63FloatValue A ) $.
verinab63-round-magnitude-graph-syntax
  $a wff ( VERINAB63RoundMagnitudeGraph A B ) $.
verinab63-round-magnitude-syntax
  $a class ( VERINAB63RoundMagnitude A ) $.
verinab63-signed-round-syntax
  $a class ( VERINAB63SignedRound A ) $.
verinab63-float-sub-graph-syntax
  $a wff ( VERINAB63FloatSubGraph A B C ) $.
verinab63-float-sub-syntax
  $a class ( VERINAB63FloatSub A B ) $.
verinab63-float-lt-syntax
  $a wff ( VERINAB63FloatLT A B ) $.
verinab63-float-le-syntax
  $a wff ( VERINAB63FloatLE A B ) $.
verinab63-get-d-syntax
  $a class ( VERINAB63GetD A B ) $.
verinab63-abs-diff-syntax
  $a class ( VERINAB63AbsDiff A B ) $.
verinab63-precondition-syntax
  $a wff ( VERINAB63Pre A B ) $.
verinab63-inner-graph-syntax
  $a wff ( VERINAB63InnerGraph A B C D ) $.
verinab63-inner-syntax
  $a class ( VERINAB63Inner A B C ) $.
verinab63-outer-graph-syntax
  $a wff ( VERINAB63OuterGraph A B C ) $.
verinab63-program-syntax
  $a class ( VERINAB63HasCloseElements A B ) $.
verinab63-pairwise-syntax
  $a wff ( VERINAB63Pairwise A B ) $.
verinab63-postcondition-syntax
  $a wff ( VERINAB63Post A B C ) $.

verinab63-float64-definition $a |- VERINAB63Float64 =
  ( 0 ..^ ( 2 ^ 6 4 ) ) $.

verinab63-sign-definition $a |- (
  VERINAB63Sign A
) = (
  |_ ` ( A / ( 2 ^ 6 3 ) )
) $.

verinab63-exponent-definition $a |- (
  VERINAB63Exponent A
) = (
  (
    |_ ` ( A / ( 2 ^ 5 2 ) )
  )
  mod
  ( 2 ^ 1 1 )
) $.

verinab63-fraction-definition $a |- (
  VERINAB63Fraction A
) = (
  A mod ( 2 ^ 5 2 )
) $.

verinab63-finite-definition $a |- (
  VERINAB63Finite A
) <-> (
  A e. VERINAB63Float64
  /\
  ( VERINAB63Exponent A ) < 2 0 4 7
) $.

verinab63-is-nan-definition $a |- (
  VERINAB63IsNaN A
) <-> (
  (
    A e. VERINAB63Float64
    /\
    ( VERINAB63Exponent A ) = 2 0 4 7
  )
  /\
  ( VERINAB63Fraction A ) =/= 0
) $.

verinab63-is-inf-definition $a |- (
  VERINAB63IsInf A
) <-> (
  (
    A e. VERINAB63Float64
    /\
    ( VERINAB63Exponent A ) = 2 0 4 7
  )
  /\
  ( VERINAB63Fraction A ) = 0
) $.

verinab63-is-zero-definition $a |- (
  VERINAB63IsZero A
) <-> (
  (
    A e. VERINAB63Float64
    /\
    ( VERINAB63Exponent A ) = 0
  )
  /\
  ( VERINAB63Fraction A ) = 0
) $.

verinab63-pos-finite-definition $a |- VERINAB63PosFinite =
  (
    0
    ..^
    ( 2 0 4 7 x. ( 2 ^ 5 2 ) )
  ) $.

verinab63-pos-inf-definition $a |- VERINAB63PosInf =
  ( 2 0 4 7 x. ( 2 ^ 5 2 ) ) $.

verinab63-neg-inf-definition $a |- VERINAB63NegInf =
  (
    ( 2 ^ 6 3 )
    +
    VERINAB63PosInf
  ) $.

${
  $d s q f A B $.

  verinab63-float-value-graph-definition $a |- (
    VERINAB63FloatValueGraph A B
  ) <-> (
    (
      ( VERINAB63Finite A )
      /\
      B e. RR
    )
    /\
    E. s e. { 0 , 1 }
      E. q e. ( 0 ..^ 2 0 4 7 )
        E. f e. ( 0 ..^ ( 2 ^ 5 2 ) )
          (
            A = (
              (
                ( s x. ( 2 ^ 6 3 ) )
                +
                ( q x. ( 2 ^ 5 2 ) )
              )
              +
              f
            )
            /\
            B = if (
              s = 0 ,
              if (
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
              ) ,
              ( -u if (
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
              ) )
            )
          )
  ) $.
$}

${
  $d x A $.

  verinab63-float-value-definition $a |- (
    VERINAB63FloatValue A
  ) = (
    iota_ x e. RR
      ( VERINAB63FloatValueGraph A x )
  ) $.
$}

${
  $d d A B $.

  verinab63-round-magnitude-graph-definition $a |- (
    VERINAB63RoundMagnitudeGraph A B
  ) <-> (
    (
      (
        A e. RR
        /\
        0 <_ A
      )
      /\
      B e. (
        VERINAB63PosFinite
        u.
        { VERINAB63PosInf }
      )
    )
    /\
    (
      (
        (
          ( ( ( 2 ^ 5 4 ) - 1 ) x. ( 2 ^ 9 7 0 ) )
          <_
          A
        )
        /\
        B = VERINAB63PosInf
      )
      \/
      (
        (
          A
          <
          ( ( ( 2 ^ 5 4 ) - 1 ) x. ( 2 ^ 9 7 0 ) )
        )
        /\
        B e. VERINAB63PosFinite
        /\
        (
          A. d e. VERINAB63PosFinite
            (
              ( A - ( VERINAB63FloatValue B ) ) ^ 2
              <_
              ( A - ( VERINAB63FloatValue d ) ) ^ 2
            )
          /\
          A. d e. VERINAB63PosFinite
            (
              (
                (
                  ( A - ( VERINAB63FloatValue B ) ) ^ 2
                  =
                  ( A - ( VERINAB63FloatValue d ) ) ^ 2
                )
                /\
                ( d mod 2 ) = 0
              )
              ->
              ( B mod 2 ) = 0
            )
        )
      )
    )
  ) $.
$}

${
  $d c A $.

  verinab63-round-magnitude-definition $a |- (
    VERINAB63RoundMagnitude A
  ) = (
    iota_ c e. (
      VERINAB63PosFinite
      u.
      { VERINAB63PosInf }
    )
      ( VERINAB63RoundMagnitudeGraph A c )
  ) $.
$}

verinab63-signed-round-definition $a |- (
  VERINAB63SignedRound A
) = if (
  A < 0 ,
  (
    ( 2 ^ 6 3 )
    +
    ( VERINAB63RoundMagnitude ( -u A ) )
  ) ,
  ( VERINAB63RoundMagnitude A )
) $.

verinab63-float-sub-graph-definition $a |- (
  VERINAB63FloatSubGraph A B C
) <-> (
  (
    (
      ( VERINAB63Finite A )
      /\
      ( VERINAB63Finite B )
    )
    /\
    C e. VERINAB63Float64
  )
  /\
  C = if (
    (
      VERINAB63FloatValue A
    ) = (
      VERINAB63FloatValue B
    ) ,
    if (
      (
        A = ( 2 ^ 6 3 )
        /\
        B = 0
      ) ,
      ( 2 ^ 6 3 ) ,
      0
    ) ,
    (
      VERINAB63SignedRound
        (
          ( VERINAB63FloatValue A )
          -
          ( VERINAB63FloatValue B )
        )
    )
  )
) $.

${
  $d c A B $.

  verinab63-float-sub-definition $a |- (
    VERINAB63FloatSub A B
  ) = (
    iota_ c e. VERINAB63Float64
      ( VERINAB63FloatSubGraph A B c )
  ) $.
$}

verinab63-float-lt-definition $a |- (
  VERINAB63FloatLT A B
) <-> (
  (
    (
      (
        A e. VERINAB63Float64
        /\
        B e. VERINAB63Float64
      )
      /\
      -. ( VERINAB63IsNaN A )
    )
    /\
    -. ( VERINAB63IsNaN B )
  )
  /\
  (
    (
      A = VERINAB63NegInf
      /\
      B =/= VERINAB63NegInf
    )
    \/
    (
      B = VERINAB63PosInf
      /\
      A =/= VERINAB63PosInf
    )
    \/
    (
      (
        ( VERINAB63Finite A )
        /\
        ( VERINAB63Finite B )
      )
      /\
      (
        ( VERINAB63FloatValue A )
        <
        ( VERINAB63FloatValue B )
      )
    )
  )
) $.

verinab63-float-le-definition $a |- (
  VERINAB63FloatLE A B
) <-> (
  (
    (
      (
        A e. VERINAB63Float64
        /\
        B e. VERINAB63Float64
      )
      /\
      -. ( VERINAB63IsNaN A )
    )
    /\
    -. ( VERINAB63IsNaN B )
  )
  /\
  (
    A = VERINAB63NegInf
    \/
    B = VERINAB63PosInf
    \/
    (
      (
        ( VERINAB63Finite A )
        /\
        ( VERINAB63Finite B )
      )
      /\
      (
        ( VERINAB63FloatValue A )
        <_
        ( VERINAB63FloatValue B )
      )
    )
  )
) $.

verinab63-get-d-definition $a |- (
  VERINAB63GetD A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab63-abs-diff-definition $a |- (
  VERINAB63AbsDiff A B
) = if (
  (
    VERINAB63FloatLT
      ( VERINAB63FloatSub A B )
      0
  ) ,
  ( VERINAB63FloatSub B A ) ,
  ( VERINAB63FloatSub A B )
) $.

${
  $d i A B $.

  verinab63-precondition-definition $a |- (
    VERINAB63Pre A B
  ) <-> (
    (
      (
        A e. Word VERINAB63Float64
        /\
        B e. VERINAB63Float64
      )
      /\
      ( VERINAB63FloatLE 0 B )
    )
    /\
    (
      -. ( VERINAB63IsNaN B )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          ( VERINAB63Finite ( A ` i ) )
        )
    )
  ) $.
$}

${
  $d k t A B C D $.

  verinab63-inner-graph-definition $a |- (
    VERINAB63InnerGraph A B C D
  ) <-> (
    (
      (
        (
          A e. Word VERINAB63Float64
          /\
          B e. VERINAB63Float64
        )
        /\
        C e. NN0
      )
      /\
      D e. { 0 , 1 }
    )
    /\
    E. t e. Word { 0 , 1 }
      (
        (
          ( # ` t ) = ( C + 1 )
          /\
          ( t ` C ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ C )
            (
              t ` k
            ) = if (
              (
                VERINAB63FloatLT
                  (
                    VERINAB63AbsDiff
                      ( VERINAB63GetD A k )
                      ( VERINAB63GetD A C )
                  )
                  B
              ) ,
              1 ,
              ( t ` ( k + 1 ) )
            )
          /\
          D = ( t ` 0 )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab63-inner-definition $a |- (
    VERINAB63Inner A B C
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINAB63InnerGraph A B C y )
  ) $.
$}

${
  $d k t A B C $.

  verinab63-outer-graph-definition $a |- (
    VERINAB63OuterGraph A B C
  ) <-> (
    (
      (
        A e. Word VERINAB63Float64
        /\
        B e. VERINAB63Float64
      )
      /\
      C e. { 0 , 1 }
    )
    /\
    E. t e. Word { 0 , 1 }
      (
        (
          ( # ` t ) = ( ( # ` A ) + 1 )
          /\
          ( t ` ( # ` A ) ) = 0
        )
        /\
        (
          A. k e. ( 0 ..^ ( # ` A ) )
            (
              t ` k
            ) = if (
              ( VERINAB63Inner A B k ) = 1 ,
              1 ,
              ( t ` ( k + 1 ) )
            )
          /\
          C = ( t ` 0 )
        )
      )
  ) $.
$}

${
  $d y A B $.

  verinab63-program-definition $a |- (
    VERINAB63HasCloseElements A B
  ) = (
    iota_ y e. { 0 , 1 }
      ( VERINAB63OuterGraph A B y )
  ) $.
$}

${
  $d i j A B $.

  verinab63-pairwise-definition $a |- (
    VERINAB63Pairwise A B
  ) <-> (
    (
      A e. Word VERINAB63Float64
      /\
      B e. VERINAB63Float64
    )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          (
            VERINAB63FloatLE
              B
              (
                VERINAB63AbsDiff
                  ( A ` i )
                  ( A ` j )
              )
          )
        )
  ) $.
$}

verinab63-postcondition-definition $a |- (
  VERINAB63Post A B C
) <-> (
  (
    (
      A e. Word VERINAB63Float64
      /\
      B e. VERINAB63Float64
    )
    /\
    C e. { 0 , 1 }
  )
  /\
  (
    C = 0
    <->
    ( VERINAB63Pairwise A B )
  )
) $.

verina-basic-63-has-close-elements $a |-
  A. w e. Word VERINAB63Float64
    A. h e. VERINAB63Float64
      (
        ( VERINAB63Pre w h )
        ->
        (
          VERINAB63Post
            w
            h
            ( VERINAB63HasCloseElements w h )
        )
      )
$.
