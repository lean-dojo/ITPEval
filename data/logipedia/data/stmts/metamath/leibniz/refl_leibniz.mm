$(
  Statement-only formalization of the Logipedia corpus artifact
  leibniz.refl_leibniz
  (logipedia__metamath__leibniz.refl_leibniz), catalog title
  "leibniz.refl_leibniz": Leibniz equality, defined by preservation of every
  predicate on an arbitrary type, is reflexive. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source type A is represented by the set-level carrier h, and
  x is bounded to h. A source predicate P : A -> Prop is represented
  extensionally by an arbitrary subset p of h. Therefore the final $a
  declaration directly unfolds leibniz A x x as preservation of membership in
  every such p. It is the native unproved statement encoding; this artifact
  introduces no $p proof declaration.
$)

${
  $d h p $.

  logipedia-leibniz-refl-leibniz $a |-
    A. h A. x e. h
      A. p e. ~P h
        ( x e. p -> x e. p )
  $.
$}
