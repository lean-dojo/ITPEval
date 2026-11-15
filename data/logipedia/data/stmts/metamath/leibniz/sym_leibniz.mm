$(
  Statement-only formalization of the Logipedia corpus artifact
  leibniz.sym_leibniz, catalog title "leibniz.sym_leibniz": symmetry of
  Leibniz equality on every type. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source type A is represented by the set-level carrier h, with
  x and y bounded to h. A source predicate P : A -> Prop is represented
  extensionally by an arbitrary subset p of h. Consequently

    A. p e. ~P h ( x e. p -> y e. p )

  is exactly the source definition of leibniz A x y. The final $a declaration
  states that this relation implies its converse for all h, x, and y. It is
  the native unproved statement encoding; this artifact's root file contains
  no $p proof declaration.
$)

${
  $d h p $.

  logipedia-leibniz-sym-leibniz $a |-
    A. h A. x e. h A. y e. h
      (
        A. p e. ~P h ( x e. p -> y e. p )
        ->
        A. p e. ~P h ( y e. p -> x e. p )
      )
  $.
$}
