$(
  Statement-only formalization of the Logipedia corpus artifact
  relations.RC_reflexive
  (logipedia__metamath__relations.RC_reflexive), catalog title
  "relations.RC_reflexive": the reflexive closure of every binary relation
  on an arbitrary type is reflexive. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A SetMM set h represents the arbitrary source type A, and
  r e. ~P ( h X. h ) ranges over every binary relation R on A. The source
  definitions unfold as

    reflexive A (RC A R)
      = forall x : A, connectives.Or (R x x) (logic.eq A x x).

  Relation application is represented by ordered-pair membership. SetMM's
  native disjunction is bidirectionally equivalent to connectives.Or:
  or_introl and or_intror give the reverse direction, while match_Or_prop
  gives the forward direction by eliminating into native disjunction.
  SetMM equality is likewise bidirectionally equivalent to logic.eq:
  logic.refl gives native-equality substitution into logic.eq, while logic.eq_ind
  with the predicate z |-> x = z sends logic.eq A x y to x = y.

  Thus the final $a declaration is the direct native rendering of the unfolded
  source proposition. It is Metamath's unproved statement encoding; this
  database contains no $p proof declaration.
$)

${
  $d h r x $.

  logipedia-relations-rc-reflexive $a |-
    A. h
      A. r e. ~P ( h X. h )
        A. x e. h
          ( <. x , x >. e. r \/ x = x )
  $.
$}
