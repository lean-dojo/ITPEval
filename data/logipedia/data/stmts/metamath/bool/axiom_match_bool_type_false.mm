$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.axiom_match_bool_type_false, catalog title
  "bool.axiom_match_bool_type_false": for every return type and pair of
  branches, Boolean elimination at false returns the false branch. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source return type is represented by the set-level carrier h,
  and the source Boolean type by the exact two-element carrier { 0 , 1 }, with
  false represented by 0. LogMatchBoolType h denotes the source polymorphic
  eliminator at carrier h. Its explicit full function-space type is

    h -> h -> { 0 , 1 } -> h.

  The following $a declaration records that typing together with the source
  false-branch equation for all two branches. It is an unproved statement
  encoding; this database contains no $p proof declaration.
$)

$c LogMatchBoolType $.

log-match-bool-type-syntax $a class ( LogMatchBoolType h ) $.

logipedia-bool-axiom-match-bool-type-false $a |-
  A. h
    (
      ( LogMatchBoolType h ) e.
        ( ( ( h ^m { 0 , 1 } ) ^m h ) ^m h )
      /\
      A. x e. h A. y e. h
        ( ( ( ( LogMatchBoolType h ) ` x ) ` y ) ` 0 ) = y
    )
$.
