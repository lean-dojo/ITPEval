$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.match_bool_prop, catalog title "bool.match_bool_prop": Boolean
  proposition elimination, where a predicate holding at true and false holds
  at every Boolean value. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source Boolean type is represented by the exact two-element carrier
  { 0 , 1 }, with true represented by 1 and false by 0. A source predicate
  return : bool -> Prop is represented extensionally by a subset p of this
  carrier, so z e. p means return z. The nested implications and final
  universal quantifier below exactly preserve the source proposition. The
  $a declaration is an unproved statement encoding; this database contains no
  $p proof declaration.
$)

logipedia-bool-match-bool-prop $a |-
  A. p e. ~P { 0 , 1 }
    (
      1 e. p
      ->
      ( 0 e. p -> A. z e. { 0 , 1 } z e. p )
    )
$.
