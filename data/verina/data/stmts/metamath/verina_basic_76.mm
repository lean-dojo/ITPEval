$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_76
  (verina__metamath__verina_basic_76), catalog title myMin: the exact
  executable strict-comparison program returns the smaller of two integers
  and satisfies its two-branch correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. VERINAB76Pre is the source True
  precondition together with the two Int input types.

  VERINAB76MyMin is exactly the executable source expression: it returns A
  when A is strictly less than B and returns B otherwise, including when the
  inputs are equal. Thus the implementation and its equality-case branch are
  fixed independently of the postcondition and admit no additional outputs.

  VERINAB76Post preserves both source implications: when A <= B the result
  equals A, and when A > B (equivalently B < A) the result equals B. The
  proof-valued precondition argument is computationally and propositionally
  unused and is represented by the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c VERINAB76Pre VERINAB76MyMin VERINAB76Post $.

verinab76-precondition-syntax
  $a wff ( VERINAB76Pre A B ) $.
verinab76-program-syntax
  $a class ( VERINAB76MyMin A B ) $.
verinab76-postcondition-syntax
  $a wff ( VERINAB76Post A B C ) $.

verinab76-precondition-definition $a |- (
  VERINAB76Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab76-program-definition $a |- (
  VERINAB76MyMin A B
) = if (
  A < B ,
  A ,
  B
) $.

verinab76-postcondition-definition $a |- (
  VERINAB76Post A B C
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
      A <_ B
      ->
      C = A
    )
    /\
    (
      B < A
      ->
      C = B
    )
  )
) $.

verina-basic-76-my-min $a |- A. x e. ZZ
  A. y e. ZZ
    (
      ( VERINAB76Pre x y )
      ->
      (
        VERINAB76Post
          x
          y
          ( VERINAB76MyMin x y )
      )
    )
$.
