$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_1
  (verina__metamath__verina_basic_1), catalog title hasOppositeSign: the exact
  executable integer product-sign test returns true precisely when its two
  inputs have opposite nonzero signs, with its Boolean correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and { 0 , 1 } represents Bool with
  false = 0 and true = 1.

  VERINAB1Pre is the source True precondition together with the two Int input
  types. VERINAB1HasOppositeSign is exactly the executable source program:
  it returns true exactly when the integer product of its inputs is negative.
  The proof-valued precondition argument is computationally unused and is
  represented by the explicit precondition antecedent in the final statement.

  VERINAB1Post preserves the source pair of implications: opposite nonzero
  signs imply a true result, while failure of that sign condition implies a
  false result. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and this
  database has no $p declaration.
$)

$c
  VERINAB1Pre VERINAB1HasOppositeSign VERINAB1Post
$.

verinab1-precondition-syntax
  $a wff ( VERINAB1Pre A B ) $.
verinab1-has-opposite-sign-syntax
  $a class ( VERINAB1HasOppositeSign A B ) $.
verinab1-postcondition-syntax
  $a wff ( VERINAB1Post A B C ) $.

verinab1-precondition-definition $a |- (
  VERINAB1Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab1-has-opposite-sign-definition $a |- (
  VERINAB1HasOppositeSign A B
) = if (
  ( A x. B ) < 0 ,
  1 ,
  0
) $.

verinab1-postcondition-definition $a |- (
  VERINAB1Post A B C
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
      (
        A < 0
        /\
        0 < B
      )
      \/
      (
        0 < A
        /\
        B < 0
      )
    )
    ->
    C = 1
  )
  /\
  (
    -.
    (
      (
        A < 0
        /\
        0 < B
      )
      \/
      (
        0 < A
        /\
        B < 0
      )
    )
    ->
    C = 0
  )
) $.

verina-basic-1-has-opposite-sign $a |- A. a e. ZZ
  A. b e. ZZ
    (
      ( VERINAB1Pre a b )
      ->
      (
        VERINAB1Post
          a
          b
          ( VERINAB1HasOppositeSign a b )
      )
    )
$.
