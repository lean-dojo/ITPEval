$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_30
  (verina__metamath__verina_basic_30), catalog title elementWiseModulo: the
  exact executable indexed integer-array map computes Lean-style Euclidean
  remainders elementwise for equal nonempty arrays with nonzero divisors and
  satisfies its output-size and pointwise-modulo correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB30GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB30IntMod is
  Lean Int.emod on all integer inputs: modulus zero returns the dividend, and
  every nonzero divisor is replaced by its positive magnitude before applying
  SetMM remainder. This preserves Lean's nonnegative Euclidean remainder
  independently of the divisor's sign.

  VERINAB30MapIdxGraph is the exact graph of
  a.mapIdx (fun i x => x % b[i]!). Its output has a.size entries and every
  valid output index contains the Euclidean remainder of the corresponding
  input entry by the bounds-defaulted entry of b. VERINAB30ElementWiseModulo
  selects the unique word described by this graph, so the executable result
  is fixed independently of the postcondition and admits no additional
  outputs.

  VERINAB30Pre preserves equal input sizes, positive size, and the universal
  nonzero-divisor condition. VERINAB30Post preserves the source result-size
  equality and its universal implication over all natural indices below the
  result size, including get!-lookup behavior. The proof-valued precondition
  arguments have no computational or propositional effect beyond the explicit
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB30GetBang VERINAB30IntMod
  VERINAB30MapIdxGraph VERINAB30ElementWiseModulo
  VERINAB30Pre VERINAB30Post
$.

verinab30-get-bang-syntax
  $a class ( VERINAB30GetBang A B ) $.
verinab30-int-mod-syntax
  $a class ( VERINAB30IntMod A B ) $.
verinab30-map-idx-graph-syntax
  $a wff ( VERINAB30MapIdxGraph A B C ) $.
verinab30-program-syntax
  $a class ( VERINAB30ElementWiseModulo A B ) $.
verinab30-precondition-syntax
  $a wff ( VERINAB30Pre A B ) $.
verinab30-postcondition-syntax
  $a wff ( VERINAB30Post A B C ) $.

verinab30-get-bang-definition $a |- (
  VERINAB30GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab30-int-mod-definition $a |- (
  VERINAB30IntMod A B
) = if (
  B = 0 ,
  A ,
  ( A mod ( abs ` B ) )
) $.

${
  $d i A B C $.

  verinab30-map-idx-graph-definition $a |- (
    VERINAB30MapIdxGraph A B C
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
    (
      ( # ` C ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          C ` i
        ) = (
          VERINAB30IntMod
            ( A ` i )
            ( VERINAB30GetBang B i )
        )
    )
  ) $.
$}

${
  $d y A B $.

  verinab30-program-definition $a |- (
    VERINAB30ElementWiseModulo A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB30MapIdxGraph A B y )
  ) $.
$}

${
  $d i A B $.

  verinab30-precondition-definition $a |- (
    VERINAB30Pre A B
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      ( # ` A ) = ( # ` B )
    )
    /\
    (
      0 < ( # ` A )
      /\
      A. i e. NN0
        (
          i < ( # ` B )
          ->
          ( VERINAB30GetBang B i ) =/= 0
        )
    )
  ) $.
$}

${
  $d i A B C $.

  verinab30-postcondition-definition $a |- (
    VERINAB30Post A B C
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
    (
      ( # ` C ) = ( # ` A )
      /\
      A. i e. NN0
        (
          i < ( # ` C )
          ->
          (
            VERINAB30GetBang C i
          ) = (
            VERINAB30IntMod
              ( VERINAB30GetBang A i )
              ( VERINAB30GetBang B i )
          )
        )
    )
  ) $.
$}

verina-basic-30-element-wise-modulo $a |- A. a e. Word ZZ
  A. b e. Word ZZ
    (
      ( VERINAB30Pre a b )
      ->
      (
        VERINAB30Post
          a
          b
          ( VERINAB30ElementWiseModulo a b )
      )
    )
$.
