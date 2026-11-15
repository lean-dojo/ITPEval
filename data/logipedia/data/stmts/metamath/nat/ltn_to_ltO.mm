$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.ltn_to_ltO (logipedia__metamath__nat.ltn_to_ltO), catalog title
  "nat.ltn_to_ltO": for all natural numbers n and m, if n is strictly less
  than m, then zero is strictly less than m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O, and its native strict
  order on NN0 represents nat.lt and is equivalent to the source definition
  nat.lt n m := nat.le (nat.S n) m. The two restricted universal quantifiers
  and implication preserve the source binder order, hypothesis, conclusion,
  and all scopes. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

logipedia-nat-ltn-to-ltO $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n < m
        ->
        0 < m
      )
$.
