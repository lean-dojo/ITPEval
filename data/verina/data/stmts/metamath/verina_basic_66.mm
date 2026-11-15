$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_66
  (verina__metamath__verina_basic_66), catalog title ComputeIsEven: the exact
  executable integer remainder test returns true precisely when its input is
  twice an integer, with its Boolean correctness contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and { 0 , 1 } represents Bool with
  false = 0 and true = 1. For the positive modulus two, SetMM's integer
  remainder agrees with Lean's Int remainder on every integer input.

  VERINAB66Pre is the source True precondition together with the Int input
  type. VERINAB66ComputeIsEven is exactly the executable source program:
  it returns one exactly when x mod 2 is zero and zero otherwise, so it admits
  no additional outputs.

  VERINAB66Post preserves the source equivalence between a true result and
  the existence of an integer k such that x = 2 * k. The proof-valued
  precondition arguments to the implementation and postcondition are
  computationally and propositionally unused beyond the explicit
  precondition antecedent in the final correctness assertion. Every earlier
  $a is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB66Pre VERINAB66ComputeIsEven VERINAB66Post
$.

verinab66-precondition-syntax
  $a wff ( VERINAB66Pre A ) $.
verinab66-program-syntax
  $a class ( VERINAB66ComputeIsEven A ) $.
verinab66-postcondition-syntax
  $a wff ( VERINAB66Post A B ) $.

verinab66-precondition-definition $a |- (
  VERINAB66Pre A
) <-> (
  A e. ZZ
) $.

verinab66-program-definition $a |- (
  VERINAB66ComputeIsEven A
) = if (
  ( A mod 2 ) = 0 ,
  1 ,
  0
) $.

${
  $d k A B $.

  verinab66-postcondition-definition $a |- (
    VERINAB66Post A B
  ) <-> (
    (
      A e. ZZ
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      B = 1
      <->
      E. k e. ZZ
        A = ( 2 x. k )
    )
  ) $.
$}

verina-basic-66-compute-is-even $a |- A. x e. ZZ
  (
    ( VERINAB66Pre x )
    ->
    (
      VERINAB66Post
        x
        ( VERINAB66ComputeIsEven x )
    )
  )
$.
