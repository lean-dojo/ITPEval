$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_99
  (verina__metamath__verina_basic_99), catalog title Triple: the exact
  executable integer program uses a threshold branch whose two computations
  both triple the input, together with its complete integer-division
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. VERINAB99FirstDouble and
  VERINAB99FirstQuadruple are exactly the source branch-local bindings
  a := 2 * x and b := 4 * x. VERINAB99ElseDouble is exactly the other
  branch's local binding y := 2 * x. Because the divisor two is positive,
  floor of SetMM rational division reproduces Lean integer division by two,
  including for negative sums. VERINAB99Triple is therefore exactly the
  source executable threshold branch, with no additional possible outputs.

  VERINAB99Pre is the source True precondition together with the Int input
  type. VERINAB99Post preserves both source conjuncts. Because the divisor
  three is positive, floor of SetMM rational division is exactly Lean's
  Euclidean integer quotient result / 3, including for negative results.
  The proof-valued precondition arguments are computationally and
  propositionally unused and are represented by the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB99FirstDouble VERINAB99FirstQuadruple VERINAB99ElseDouble
  VERINAB99Pre VERINAB99Triple VERINAB99Post
$.

verinab99-first-double-syntax
  $a class ( VERINAB99FirstDouble A ) $.
verinab99-first-quadruple-syntax
  $a class ( VERINAB99FirstQuadruple A ) $.
verinab99-else-double-syntax
  $a class ( VERINAB99ElseDouble A ) $.
verinab99-precondition-syntax
  $a wff ( VERINAB99Pre A ) $.
verinab99-program-syntax
  $a class ( VERINAB99Triple A ) $.
verinab99-postcondition-syntax
  $a wff ( VERINAB99Post A B ) $.

verinab99-first-double-definition $a |- (
  VERINAB99FirstDouble A
) = (
  2 x. A
) $.

verinab99-first-quadruple-definition $a |- (
  VERINAB99FirstQuadruple A
) = (
  4 x. A
) $.

verinab99-else-double-definition $a |- (
  VERINAB99ElseDouble A
) = (
  2 x. A
) $.

verinab99-precondition-definition $a |- (
  VERINAB99Pre A
) <-> (
  A e. ZZ
) $.

verinab99-program-definition $a |- (
  VERINAB99Triple A
) = if (
  A < ; 1 8 ,
  (
    |_ ` (
      (
        ( VERINAB99FirstDouble A )
        +
        ( VERINAB99FirstQuadruple A )
      ) / 2
    )
  ) ,
  A + ( VERINAB99ElseDouble A )
) $.

verinab99-postcondition-definition $a |- (
  VERINAB99Post A B
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

verina-basic-99-triple $a |- A. x e. ZZ
  (
    ( VERINAB99Pre x )
    ->
    (
      VERINAB99Post
        x
        ( VERINAB99Triple x )
    )
  )
$.
