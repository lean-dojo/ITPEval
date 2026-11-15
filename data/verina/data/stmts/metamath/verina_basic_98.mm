$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_98
  (verina__metamath__verina_basic_98), catalog title Triple: the exact
  executable integer program multiplies its input by three and satisfies its
  complete integer-division correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. VERINAB98Pre is the source True
  precondition together with the Int input type. VERINAB98Triple is exactly
  the source executable expression x * 3, so its output is fixed independently
  of the postcondition and it admits no additional results.

  VERINAB98Post preserves both source conjuncts. Because the divisor three is
  positive, floor of SetMM rational division is exactly Lean's Euclidean
  integer quotient result / 3, including for negative results. The
  proof-valued precondition arguments are computationally and propositionally
  unused and are represented by the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c VERINAB98Pre VERINAB98Triple VERINAB98Post $.

verinab98-precondition-syntax
  $a wff ( VERINAB98Pre A ) $.
verinab98-program-syntax
  $a class ( VERINAB98Triple A ) $.
verinab98-postcondition-syntax
  $a wff ( VERINAB98Post A B ) $.

verinab98-precondition-definition $a |- (
  VERINAB98Pre A
) <-> (
  A e. ZZ
) $.

verinab98-program-definition $a |- (
  VERINAB98Triple A
) = (
  A x. 3
) $.

verinab98-postcondition-definition $a |- (
  VERINAB98Post A B
) <-> (
  (
    A e. ZZ
    /\
    B e. ZZ
  )
  /\
  (
    ( |_ ` ( B / 3 ) ) = A
    /\
    ( ( |_ ` ( B / 3 ) ) x. 3 ) = B
  )
) $.

verina-basic-98-triple $a |- A. x e. ZZ
  (
    ( VERINAB98Pre x )
    ->
    (
      VERINAB98Post
        x
        ( VERINAB98Triple x )
    )
  )
$.
