$(
  Statement-only formalization of the Logipedia corpus artifact
  bool.bool_discr, catalog title "bool.bool_discr": equality of two Boolean
  values makes the corresponding nested Boolean case analysis select the
  universally valid proposition. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source Boolean type is represented by the exact two-element carrier
  { 0 , 1 }, with true represented by 1 and false by 0. The two closed source
  propositions ( forall P, P -> P ) and ( forall P, P ) have exact truth
  values 1 and 0, respectively. Thus the nested SetMM conditionals below are
  the source proposition-valued Boolean eliminators, and equality to 1 asserts
  that their selected proposition holds. The following $a declaration is an
  unproved statement encoding; this database contains no $p proof declaration.
$)

logipedia-bool-bool-discr $a |-
  A. x e. { 0 , 1 } A. y e. { 0 , 1 }
    (
      x = y
      ->
      if (
        x = 1 ,
        if ( y = 1 , 1 , 0 ) ,
        if ( y = 1 , 0 , 1 )
      ) = 1
    )
$.
