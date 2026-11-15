$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.eq_match_bool_type_true, catalog title
  "bool.eq_match_bool_type_true": for every return type and pair of branches,
  Boolean elimination at true is Leibniz equal to the true branch. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source return type is represented by the set-level carrier h,
  and the source Boolean type by the exact two-element carrier { 0 , 1 }, with
  true represented by 1. LogMatchBoolType h denotes the source polymorphic
  eliminator and has the full curried function-space type

    h -> h -> { 0 , 1 } -> h.

  A predicate on h is represented extensionally by a subset p. Thus the
  bounded universal implication is exactly the source definition of Leibniz
  equality: every predicate holding of the result of elimination at true also
  holds of the true branch. The final declaration is an unproved $a statement
  encoding; this artifact file contains no $p proof declaration.
$)

$c LogMatchBoolType $.

log-match-bool-type-syntax $a class ( LogMatchBoolType h ) $.

${
  $d h p $.

  logipedia-bool-eq-match-bool-type-true $a |-
    A. h
      (
        ( LogMatchBoolType h ) e.
          ( ( ( h ^m { 0 , 1 } ) ^m h ) ^m h )
        /\
        A. x e. h A. y e. h A. p e. ~P h
          (
            ( ( ( ( LogMatchBoolType h ) ` x ) ` y ) ` 1 ) e. p
            ->
            x e. p
          )
      )
  $.
$}
