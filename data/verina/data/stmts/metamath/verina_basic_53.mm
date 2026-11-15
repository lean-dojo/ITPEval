$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_53
  (verina__metamath__verina_basic_53), catalog title CalSum: the exact
  natural-number recursion sums the integers from one through N and satisfies
  the closed-form correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain. For N in NN0, the finite sum
  over 0 ..^ ( N + 1 ) adds exactly 0, 1, ..., N using natural addition.

  VERINAB53Loop is definitionally equivalent to the source local recursion:
  at zero its only summand is zero, and extending the range from N to N + 1
  adds the new summand N + 1. VERINAB53CalSum invokes that helper unchanged,
  so the executable result is fixed independently of the postcondition and
  no additional outputs are admitted.

  VERINAB53Pre is the source True precondition together with the Nat input
  type. VERINAB53Post preserves the Nat result type and the exact source
  equation 2 * result = N * (N + 1). The proof-valued precondition arguments
  to the implementation and postcondition are computationally and
  propositionally unused beyond the explicit antecedent in the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c
  VERINAB53Loop VERINAB53Pre VERINAB53CalSum VERINAB53Post
$.

verinab53-loop-syntax
  $a class ( VERINAB53Loop A ) $.
verinab53-precondition-syntax
  $a wff ( VERINAB53Pre A ) $.
verinab53-program-syntax
  $a class ( VERINAB53CalSum A ) $.
verinab53-postcondition-syntax
  $a wff ( VERINAB53Post A B ) $.

${
  $d k A $.

  verinab53-loop-definition $a |- (
    VERINAB53Loop A
  ) = (
    sum_ k e. ( 0 ..^ ( A + 1 ) ) k
  ) $.
$}

verinab53-precondition-definition $a |- (
  VERINAB53Pre A
) <-> (
  A e. NN0
) $.

verinab53-program-definition $a |- (
  VERINAB53CalSum A
) = (
  VERINAB53Loop A
) $.

verinab53-postcondition-definition $a |- (
  VERINAB53Post A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    ( 2 x. B )
    =
    ( A x. ( A + 1 ) )
  )
) $.

verina-basic-53-cal-sum $a |- A. n e. NN0
  (
    ( VERINAB53Pre n )
    ->
    (
      VERINAB53Post
        n
        ( VERINAB53CalSum n )
    )
  )
$.
