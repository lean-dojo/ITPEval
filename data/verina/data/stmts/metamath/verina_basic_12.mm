$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_12
  (verina__metamath__verina_basic_12), catalog title cubeSurfaceArea: the
  exact executable natural-number program computes the surface area of a cube
  as six times the square of its edge length and satisfies its two-sided
  truncated-subtraction correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain. VERINAB12NatSub is Lean's
  truncated natural subtraction. VERINAB12Pre is the source True
  precondition together with the Nat input type.

  VERINAB12CubeSurfaceArea is exactly the executable source expression
  (6 * size) * size, preserving its left-associated multiplication.
  VERINAB12Post preserves the source conjunction that both truncated
  differences between the result and that expression are zero. Thus the
  implementation is fixed independently of the postcondition and permits no
  additional outputs.

  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB12NatSub VERINAB12Pre VERINAB12CubeSurfaceArea VERINAB12Post
$.

verinab12-nat-sub-syntax
  $a class ( VERINAB12NatSub A B ) $.
verinab12-precondition-syntax
  $a wff ( VERINAB12Pre A ) $.
verinab12-program-syntax
  $a class ( VERINAB12CubeSurfaceArea A ) $.
verinab12-postcondition-syntax
  $a wff ( VERINAB12Post A B ) $.

verinab12-nat-sub-definition $a |- (
  VERINAB12NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab12-precondition-definition $a |- (
  VERINAB12Pre A
) <-> (
  A e. NN0
) $.

verinab12-program-definition $a |- (
  VERINAB12CubeSurfaceArea A
) = (
  ( 6 x. A ) x. A
) $.

verinab12-postcondition-definition $a |- (
  VERINAB12Post A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    (
      VERINAB12NatSub
        B
        ( ( 6 x. A ) x. A )
    ) = 0
    /\
    (
      VERINAB12NatSub
        ( ( 6 x. A ) x. A )
        B
    ) = 0
  )
) $.

verina-basic-12-cube-surface-area $a |- A. n e. NN0
  (
    ( VERINAB12Pre n )
    ->
    (
      VERINAB12Post
        n
        ( VERINAB12CubeSurfaceArea n )
    )
  )
$.
