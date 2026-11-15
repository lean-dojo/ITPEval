$(
  Statement-only formalization of "The Triangle Inequality" from the Hundred
  Theorems corpus artifact 091: in an arbitrary seminormed group, the
  seminorm of a sum is at most the sum of the seminorms. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  A seminormed group is represented equivalently by a group W together with
  a finite-valued pseudometric D on its carrier that is invariant under every
  right translation. No metric separation axiom is imposed: distinct points
  may have distance zero. The seminorm is definitionally D(x, 0), where 0 is
  the group identity.

  The variables W, D, A, and B are schematic and therefore universally
  quantified subject to the displayed hypotheses. The bound variables x, y,
  and z express translation invariance on the entire carrier.
$)

$d A x y z $.
$d B x y z $.
$d D x y z $.
$d W x y z $.

hundred-theorems-091-triangle-inequality $a |- (
  (
    W e. Grp
    /\
    (
      D e. ( PsMet ` ( Base ` W ) )
      /\
      (
        D : ( ( Base ` W ) X. ( Base ` W ) ) --> RR
        /\
        (
          (
            A. x e. ( Base ` W )
            A. y e. ( Base ` W )
            A. z e. ( Base ` W )
            (
              ( ( x ( +g ` W ) z ) D ( y ( +g ` W ) z ) )
              =
              ( x D y )
            )
          )
          /\
          ( A e. ( Base ` W ) /\ B e. ( Base ` W ) )
        )
      )
    )
  )
  ->
  (
    ( ( A ( +g ` W ) B ) D ( 0g ` W ) )
    <_
    ( ( A D ( 0g ` W ) ) + ( B D ( 0g ` W ) ) )
  )
) $.
