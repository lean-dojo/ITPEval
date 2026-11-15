$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_13
  (verina__metamath__verina_basic_13), catalog title cubeElements: the exact
  executable integer-array map replaces every entry by its left-associated
  integer cube and satisfies the equal-length, pointwise correctness contract
  for arbitrary finite integer arrays. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer arrays. For a word w, # ` w is its natural-number
  length, w ` i is zero-based lookup, and 0 ..^ ( # ` w ) is its complete
  index set.

  VERINAB13CubeMapGraph is the exact graph of the source Array.map: it fixes
  the output length and maps every valid index i to
  ((input[i] * input[i]) * input[i]), preserving Lean's left-associated
  expression x * x * x. VERINAB13CubeElements selects the unique finite word
  described by that graph, so the executable result is fixed independently
  of the postcondition and admits no additional outputs.

  VERINAB13Pre is the source True precondition on typed Array Int inputs.
  VERINAB13Post preserves the source size equality and universal valid-index
  get!-equality; under its index bound, SetMM word lookup is exactly Lean
  Array.get! lookup. The proof-valued precondition argument is computationally
  and propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB13CubeMapGraph VERINAB13CubeElements
  VERINAB13Pre VERINAB13Post
$.

verinab13-cube-map-graph-syntax
  $a wff ( VERINAB13CubeMapGraph A B ) $.
verinab13-program-syntax
  $a class ( VERINAB13CubeElements A ) $.
verinab13-precondition-syntax
  $a wff ( VERINAB13Pre A ) $.
verinab13-postcondition-syntax
  $a wff ( VERINAB13Post A B ) $.

${
  $d i A B $.

  verinab13-cube-map-graph-definition $a |- (
    VERINAB13CubeMapGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` i
        ) = (
          (
            ( A ` i )
            x.
            ( A ` i )
          )
          x.
          ( A ` i )
        )
    )
  ) $.
$}

${
  $d y A $.

  verinab13-program-definition $a |- (
    VERINAB13CubeElements A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB13CubeMapGraph A y )
  ) $.
$}

verinab13-precondition-definition $a |- (
  VERINAB13Pre A
) <-> (
  A e. Word ZZ
) $.

${
  $d i A B $.

  verinab13-postcondition-definition $a |- (
    VERINAB13Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          B ` i
        ) = (
          (
            ( A ` i )
            x.
            ( A ` i )
          )
          x.
          ( A ` i )
        )
    )
  ) $.
$}

verina-basic-13-cube-elements $a |- A. w e. Word ZZ
  (
    ( VERINAB13Pre w )
    ->
    (
      VERINAB13Post
        w
        ( VERINAB13CubeElements w )
    )
  )
$.
