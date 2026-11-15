$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.sym_eq_match_bool_type_false, catalog title
  "bool.sym_eq_match_bool_type_false": for every return type and pair of
  branches, the false branch is Leibniz equal to Boolean elimination at false.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source return type is represented by the set-level carrier h,
  and the source Boolean type by the exact two-element carrier { 0 , 1 }, with
  false represented by 0. LogMatchBoolType h denotes the source polymorphic
  eliminator and has the full curried function-space type

    h -> h -> { 0 , 1 } -> h.

  A predicate on h is represented extensionally by a subset p. Thus the
  bounded universal implication is exactly the source definition of Leibniz
  equality: every predicate holding of the false branch also holds of the
  result of elimination at false. The final declaration is an unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

$c LogMatchBoolType $.

log-match-bool-type-syntax $a class ( LogMatchBoolType h ) $.

${
  $d h p $.

  logipedia-bool-sym-eq-match-bool-type-false $a |-
    A. h
      (
        ( LogMatchBoolType h ) e.
          ( ( ( h ^m { 0 , 1 } ) ^m h ) ^m h )
        /\
        A. x e. h A. y e. h A. p e. ~P h
          (
            y e. p
            ->
            ( ( ( ( LogMatchBoolType h ) ` x ) ` y ) ` 0 ) e. p
          )
      )
  $.
$}
