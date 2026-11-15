$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.transitive_lt (logipedia__metamath__nat.transitive_lt), catalog title
  "nat.transitive_lt": strict order on natural numbers is transitive.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. The source defines nat.lt n m as nat.le (nat.S n) m;
  SetMM's native strict order on NN0 is equivalent to that definition.
  Expanding relations.transitive gives three restricted universal quantifiers
  followed by the two nested strict-order assumptions and their conclusion,
  preserving the source binder order and scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

logipedia-nat-transitive-lt $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        (
          n < m
          ->
          (
            m < p
            ->
            n < p
          )
        )
$.
