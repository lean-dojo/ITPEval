$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_5
  (verina__metamath__verina_basic_5), catalog title multiply: the exact
  executable integer program returns the product of its two inputs and
  satisfies its two-sided subtraction correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. VERINAB5Pre is the source True
  precondition together with the two Int input types.

  VERINAB5Multiply is exactly the executable source expression a * b.
  VERINAB5Post preserves the source conjunction that the result minus the
  product and the product minus the result are both zero. Thus the
  implementation is fixed independently of the postcondition and permits no
  additional outputs.

  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB5Pre VERINAB5Multiply VERINAB5Post
$.

verinab5-precondition-syntax
  $a wff ( VERINAB5Pre A B ) $.
verinab5-program-syntax
  $a class ( VERINAB5Multiply A B ) $.
verinab5-postcondition-syntax
  $a wff ( VERINAB5Post A B C ) $.

verinab5-precondition-definition $a |- (
  VERINAB5Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab5-program-definition $a |- (
  VERINAB5Multiply A B
) = (
  A x. B
) $.

verinab5-postcondition-definition $a |- (
  VERINAB5Post A B C
) <-> (
  (
    (
      A e. ZZ
      /\
      B e. ZZ
    )
    /\
    C e. ZZ
  )
  /\
  (
    (
      C - ( A x. B )
    ) = 0
    /\
    (
      ( A x. B ) - C
    ) = 0
  )
) $.

verina-basic-5-multiply $a |- A. a e. ZZ
  A. b e. ZZ
    (
      ( VERINAB5Pre a b )
      ->
      (
        VERINAB5Post
          a
          b
          ( VERINAB5Multiply a b )
      )
    )
$.
