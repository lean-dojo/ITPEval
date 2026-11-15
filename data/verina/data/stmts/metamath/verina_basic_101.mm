$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_101 (verina__metamath__verina_basic_101), catalog title Triple:
  the exact executable integer program doubles its input and then adds the
  original input, together with its integer-division correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. For an integer A,
  VERINAB101Twice A is the source local binding y := x * 2, and
  VERINAB101Triple A is exactly the executable source expression y + x.

  VERINAB101Pre is the source True precondition together with the Int input
  type. VERINAB101Post preserves both source conjuncts. Because the divisor
  three is positive, floor of SetMM rational division is exactly Lean's
  Euclidean integer quotient result / 3, including for negative results.
  The proof-valued precondition arguments are computationally and
  propositionally unused and are represented by the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB101Twice VERINAB101Pre VERINAB101Triple VERINAB101Post
$.

verinab101-twice-syntax
  $a class ( VERINAB101Twice A ) $.
verinab101-precondition-syntax
  $a wff ( VERINAB101Pre A ) $.
verinab101-program-syntax
  $a class ( VERINAB101Triple A ) $.
verinab101-postcondition-syntax
  $a wff ( VERINAB101Post A B ) $.

verinab101-twice-definition $a |- (
  VERINAB101Twice A
) = (
  A x. 2
) $.

verinab101-precondition-definition $a |- (
  VERINAB101Pre A
) <-> (
  A e. ZZ
) $.

verinab101-program-definition $a |- (
  VERINAB101Triple A
) = (
  ( VERINAB101Twice A ) + A
) $.

verinab101-postcondition-definition $a |- (
  VERINAB101Post A B
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

verina-basic-101-triple $a |- A. x e. ZZ
  (
    ( VERINAB101Pre x )
    ->
    (
      VERINAB101Post
        x
        ( VERINAB101Triple x )
    )
  )
$.
