$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_9
  (verina__metamath__verina_basic_9), catalog title hasCommonElement: the
  exact executable nested integer-array scan returns true precisely when the
  two nonempty arrays have an equal pair of entries, and satisfies the source
  indexed-existence Boolean correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer arrays. For a word w, # ` w is its natural-number
  length, w ` i is zero-based lookup, and 0 ..^ ( # ` w ) is its complete
  valid-index set. The Boolean domain is represented by { 0 , 1 }, with false
  = 0 and true = 1.

  VERINAB9GetBang reproduces Lean Array.get! on integer arrays, including its
  inhabited default value zero outside the valid index range.
  VERINAB9HasCommon is true exactly when a valid entry of the first array
  equals a valid entry of the second. This bounded existential is the exact
  truth condition computed by the pure nested Array.any calls.
  VERINAB9HasCommonElement returns one precisely in that case and zero
  otherwise, so the executable result is fixed independently of the
  postcondition and admits no additional outputs.

  VERINAB9Pre preserves both positive-size assumptions. VERINAB9Post retains
  the source natural-number witnesses, their explicit bounds, both get!
  lookups, and equivalence with the Boolean result. The proof-valued
  precondition argument is computationally and propositionally unused and is
  represented by the explicit antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB9GetBang VERINAB9HasCommon
  VERINAB9Pre VERINAB9HasCommonElement VERINAB9Post
$.

verinab9-get-bang-syntax
  $a class ( VERINAB9GetBang A B ) $.
verinab9-has-common-syntax
  $a wff ( VERINAB9HasCommon A B ) $.
verinab9-precondition-syntax
  $a wff ( VERINAB9Pre A B ) $.
verinab9-program-syntax
  $a class ( VERINAB9HasCommonElement A B ) $.
verinab9-postcondition-syntax
  $a wff ( VERINAB9Post A B C ) $.

verinab9-get-bang-definition $a |- (
  VERINAB9GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i j A B $.

  verinab9-has-common-definition $a |- (
    VERINAB9HasCommon A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      E. j e. ( 0 ..^ ( # ` B ) )
        ( A ` i ) = ( B ` j )
  ) $.
$}

verinab9-precondition-definition $a |- (
  VERINAB9Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    0 < ( # ` A )
    /\
    0 < ( # ` B )
  )
) $.

verinab9-program-definition $a |- (
  VERINAB9HasCommonElement A B
) = if (
  ( VERINAB9HasCommon A B ) ,
  1 ,
  0
) $.

${
  $d i j A B C $.

  verinab9-postcondition-definition $a |- (
    VERINAB9Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. { 0 , 1 }
    )
    /\
    (
      E. i e. NN0
        E. j e. NN0
          (
            (
              i < ( # ` A )
              /\
              j < ( # ` B )
            )
            /\
            (
              VERINAB9GetBang A i
            ) = (
              VERINAB9GetBang B j
            )
          )
      <->
      C = 1
    )
  ) $.
$}

verina-basic-9-has-common-element $a |- A. a e. Word ZZ
  A. b e. Word ZZ
    (
      ( VERINAB9Pre a b )
      ->
      (
        VERINAB9Post
          a
          b
          ( VERINAB9HasCommonElement a b )
      )
    )
$.
