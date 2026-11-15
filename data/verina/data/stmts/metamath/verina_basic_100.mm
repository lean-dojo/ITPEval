$(
  Statement-only formalization of the VERINA corpus artifact
  verina_basic_100 (verina__metamath__verina_basic_100), catalog title Triple:
  the exact executable integer program returns zero at zero and otherwise
  adds its input to twice itself, together with its integer-division
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. For an integer A, VERINAB100Twice A
  is the source local binding y := 2 * x. VERINAB100Triple is exactly the
  executable source branch: zero maps to zero, and every nonzero input maps
  to x + y.

  VERINAB100Pre is the source True precondition together with the Int input
  type. VERINAB100Post preserves both source conjuncts. Because the divisor
  three is positive, floor of SetMM rational division is exactly Lean's
  Euclidean integer quotient result / 3, including for negative results.
  The proof-valued precondition arguments are computationally and
  propositionally unused and are represented by the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB100Twice VERINAB100Pre VERINAB100Triple VERINAB100Post
$.

verinab100-twice-syntax
  $a class ( VERINAB100Twice A ) $.
verinab100-precondition-syntax
  $a wff ( VERINAB100Pre A ) $.
verinab100-program-syntax
  $a class ( VERINAB100Triple A ) $.
verinab100-postcondition-syntax
  $a wff ( VERINAB100Post A B ) $.

verinab100-twice-definition $a |- (
  VERINAB100Twice A
) = (
  2 x. A
) $.

verinab100-precondition-definition $a |- (
  VERINAB100Pre A
) <-> (
  A e. ZZ
) $.

verinab100-program-definition $a |- (
  VERINAB100Triple A
) = if (
  A = 0 ,
  0 ,
  A + ( VERINAB100Twice A )
) $.

verinab100-postcondition-definition $a |- (
  VERINAB100Post A B
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

verina-basic-100-triple $a |- A. x e. ZZ
  (
    ( VERINAB100Pre x )
    ->
    (
      VERINAB100Post
        x
        ( VERINAB100Triple x )
    )
  )
$.
