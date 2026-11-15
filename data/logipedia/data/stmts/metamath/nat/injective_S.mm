$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.injective_S (logipedia__metamath__nat.injective_S), catalog title
  "nat.injective_S": the natural-number successor function is injective.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. Adding one represents the source successor
  constructor nat.S, and native equality represents source natural-number
  equality. Expanding relations.injective gives the two restricted universal
  quantifiers and the implication from equality of successors to equality of
  their inputs. The final declaration is Metamath's native unproved $a
  statement encoding; this artifact adds no $p proof declaration.
$)

${
  $d x y $.

  logipedia-nat-injective-s $a |-
    A. x e. NN0
      A. y e. NN0
        (
          ( x + 1 ) = ( y + 1 )
          ->
          x = y
        )
  $.
$}
