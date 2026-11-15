$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_55
  (verina__metamath__verina_basic_55), catalog title Compare: the exact
  executable integer-equality test returns true exactly when its two inputs
  are equal and false otherwise, together with its precondition and Boolean
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and { 0 , 1 } represents Bool with
  false = 0 and true = 1.

  VERINAB55Pre is the source True precondition together with the two Int input
  types. VERINAB55Compare is exactly the source executable conditional: it
  returns one when the two integers are equal and zero otherwise, so it admits
  no additional outputs. VERINAB55Post preserves both source implications:
  equal inputs imply a true result, and unequal inputs imply a false result.

  The proof-valued precondition arguments to the implementation and
  postcondition are computationally and propositionally unused beyond the
  explicit precondition antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB55Pre VERINAB55Compare VERINAB55Post
$.

verinab55-precondition-syntax
  $a wff ( VERINAB55Pre A B ) $.
verinab55-program-syntax
  $a class ( VERINAB55Compare A B ) $.
verinab55-postcondition-syntax
  $a wff ( VERINAB55Post A B C ) $.

verinab55-precondition-definition $a |- (
  VERINAB55Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab55-program-definition $a |- (
  VERINAB55Compare A B
) = if (
  A = B ,
  1 ,
  0
) $.

verinab55-postcondition-definition $a |- (
  VERINAB55Post A B C
) <-> (
  (
    (
      A e. ZZ
      /\
      B e. ZZ
    )
    /\
    C e. { 0 , 1 }
  )
  /\
  (
    (
      A = B
      ->
      C = 1
    )
    /\
    (
      A =/= B
      ->
      C = 0
    )
  )
) $.

verina-basic-55-compare $a |- A. a e. ZZ
  A. b e. ZZ
    (
      ( VERINAB55Pre a b )
      ->
      (
        VERINAB55Post
          a
          b
          ( VERINAB55Compare a b )
      )
    )
$.
