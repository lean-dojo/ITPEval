$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_108 (verina__metamath__verina_basic_108), catalog title
  below_zero: the exact cumulative-sum program returns all integer prefix
  sums and a Boolean flag indicating whether any computed sum is negative,
  together with its array-shape and sign correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists and arrays, represented extensionally by
  their entries. For a word w, # ` w is its natural-number length, w ` i is
  zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set. The
  Boolean domain is represented by { 0 , 1 }, with false = 0 and true = 1.

  VERINAB108BuildSGraph is the exact graph of the source buildS fold. It
  starts with zero and has one further entry per operation, each obtained by
  adding that operation to the preceding entry. The accumulator is always
  nonempty, so this recurrence exactly reproduces getLast?.getD 0 followed by
  append. VERINAB108BuildS selects the unique resulting word.

  VERINAB108HasNegative is true exactly when some entry of its input word is
  negative. VERINAB108CheckNegative returns one in that case and zero
  otherwise. This is exactly the result of the source structural recursion
  over buildS.toList, including the empty-list base case, and permits no
  additional result.

  VERINAB108Pre is the source True precondition together with the List Int
  input type. VERINAB108BelowZero pairs the exact buildS output with the exact
  check_negative result. VERINAB108Post preserves the source result type,
  output length, initial zero, complete prefix-sum recurrence, true-result
  implication, and false-result nonnegativity implication. Under the length
  conjunct, its direct indexed equalities are equivalent to the source
  optional and bounds-defaulted accesses.

  The proof-valued precondition argument has no computational effect and the
  postcondition does not inspect it, so the final correctness assertion
  represents it by its explicit precondition antecedent. Every earlier $a is
  syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB108BuildSGraph VERINAB108BuildS
  VERINAB108HasNegative VERINAB108CheckNegative
  VERINAB108Pre VERINAB108BelowZero VERINAB108Post
$.

verinab108-build-s-graph-syntax
  $a wff ( VERINAB108BuildSGraph A B ) $.
verinab108-build-s-syntax
  $a class ( VERINAB108BuildS A ) $.
verinab108-has-negative-syntax
  $a wff ( VERINAB108HasNegative A ) $.
verinab108-check-negative-syntax
  $a class ( VERINAB108CheckNegative A ) $.
verinab108-precondition-syntax
  $a wff ( VERINAB108Pre A ) $.
verinab108-program-syntax
  $a class ( VERINAB108BelowZero A ) $.
verinab108-postcondition-syntax
  $a wff ( VERINAB108Post A B ) $.

${
  $d i A B $.

  verinab108-build-s-graph-definition $a |- (
    VERINAB108BuildSGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( ( # ` A ) + 1 )
      /\
      (
        ( B ` 0 ) = 0
        /\
        A. i e. ( 0 ..^ ( # ` A ) )
          (
            B ` ( i + 1 )
          ) = (
            ( B ` i ) + ( A ` i )
          )
      )
    )
  ) $.
$}

${
  $d s A $.

  verinab108-build-s-definition $a |- (
    VERINAB108BuildS A
  ) = (
    iota_ s e. Word ZZ
      ( VERINAB108BuildSGraph A s )
  ) $.
$}

${
  $d i A $.

  verinab108-has-negative-definition $a |- (
    VERINAB108HasNegative A
  ) <-> (
    A e. Word ZZ
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      ( A ` i ) < 0
  ) $.
$}

verinab108-check-negative-definition $a |- (
  VERINAB108CheckNegative A
) = if (
  ( VERINAB108HasNegative A ) ,
  1 ,
  0
) $.

verinab108-precondition-definition $a |- (
  VERINAB108Pre A
) <-> (
  A e. Word ZZ
) $.

verinab108-program-definition $a |- (
  VERINAB108BelowZero A
) = <.
  ( VERINAB108BuildS A )
  ,
  (
    VERINAB108CheckNegative
      ( VERINAB108BuildS A )
  )
>. $.

${
  $d i A B $.

  verinab108-postcondition-definition $a |- (
    VERINAB108Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. ( Word ZZ X. { 0 , 1 } )
    )
    /\
    (
      (
        # ` ( 1st ` B )
      ) = (
        ( # ` A ) + 1
      )
      /\
      (
        ( ( 1st ` B ) ` 0 ) = 0
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              ( 1st ` B ) ` ( i + 1 )
            ) = (
              ( ( 1st ` B ) ` i )
              +
              ( A ` i )
            )
          /\
          (
            (
              ( 2nd ` B ) = 1
              ->
              E. i e. ( 0 ..^ ( # ` A ) )
                ( ( 1st ` B ) ` ( i + 1 ) ) < 0
            )
            /\
            (
              ( 2nd ` B ) = 0
              ->
              A. i e. ( 0 ..^ ( # ` ( 1st ` B ) ) )
                0 <_ ( ( 1st ` B ) ` i )
            )
          )
        )
      )
    )
  ) $.
$}

verina-basic-108-below-zero $a |- A. w e. Word ZZ
  (
    ( VERINAB108Pre w )
    ->
    (
      VERINAB108Post
        w
        ( VERINAB108BelowZero w )
    )
  )
$.
