$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.axiom_match_bool_type_true, catalog title
  "bool.axiom_match_bool_type_true": for every return type and pair of
  branches, Boolean elimination at true returns the true branch. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The arbitrary source return type is represented by the set-level carrier h,
  and the source Boolean type by the exact two-element carrier { 0 , 1 }, with
  true represented by 1. LogMatchBoolType h denotes the source polymorphic
  eliminator at carrier h. Its explicit full function-space type is

    h -> h -> { 0 , 1 } -> h.

  The following $a declaration records that typing together with the source
  true-branch equation for all two branches. It is an unproved statement
  encoding; this database contains no $p proof declaration.
$)

$c LogMatchBoolType $.

log-match-bool-type-syntax $a class ( LogMatchBoolType h ) $.

logipedia-bool-axiom-match-bool-type-true $a |-
  A. h
    (
      ( LogMatchBoolType h ) e.
        ( ( ( h ^m { 0 , 1 } ) ^m h ) ^m h )
      /\
      A. x e. h A. y e. h
        ( ( ( ( LogMatchBoolType h ) ` x ) ` y ) ` 1 ) = x
    )
$.
