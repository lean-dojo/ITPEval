$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.eq_match_bool_type_false, catalog title
  "bool.eq_match_bool_type_false": for every return type and pair of branches,
  Boolean elimination at false is Leibniz equal to the false branch. This file
  contains no proof.
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
  equality: every predicate holding of the result of elimination at false
  also holds of the false branch. The explicit function-space conjunct
  preserves the source declaration's polymorphic eliminator type. The final
  declaration is an unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

$c LogMatchBoolType $.

log-match-bool-type-syntax $a class ( LogMatchBoolType h ) $.

${
  $d h p $.

  logipedia-bool-eq-match-bool-type-false $a |-
    A. h
      (
        ( LogMatchBoolType h ) e.
          ( ( ( h ^m { 0 , 1 } ) ^m h ) ^m h )
        /\
        A. x e. h A. y e. h A. p e. ~P h
          (
            ( ( ( ( LogMatchBoolType h ) ` x ) ` y ) ` 0 ) e. p
            ->
            y e. p
          )
      )
  $.
$}
