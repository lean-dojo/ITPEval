$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.transitive_le (logipedia__metamath__nat.transitive_le), catalog title
  "nat.transitive_le": non-strict order on natural numbers is transitive.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's native non-strict order on NN0 represents
  nat.le. Expanding relations.transitive gives three restricted universal
  quantifiers followed by the two nested order assumptions and their
  conclusion, preserving the source binder order and scopes. The final
  declaration is Metamath's native unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

logipedia-nat-transitive-le $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        (
          n <_ m
          ->
          (
            m <_ p
            ->
            n <_ p
          )
        )
$.
