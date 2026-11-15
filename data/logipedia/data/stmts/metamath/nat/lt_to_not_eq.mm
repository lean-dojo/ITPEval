$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_to_not_eq (logipedia__metamath__nat.lt_to_not_eq), catalog title
  "nat.lt_to_not_eq": for all natural numbers n and m, if n is strictly less
  than m, then n and m are not equal. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's native strict order on NN0 represents nat.lt
  and is equivalent to the source definition nat.lt n m := nat.le (nat.S n)
  m. Native SetMM equality represents source natural-number equality, and
  native negation represents connectives.Not. The two restricted universal
  quantifiers and implication preserve the source binder order, hypothesis,
  conclusion, and all scopes. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

logipedia-nat-lt-to-not-eq $a |-
  A. n e. NN0
    A. m e. NN0
      (
        n < m
        ->
        -. n = m
      )
$.
