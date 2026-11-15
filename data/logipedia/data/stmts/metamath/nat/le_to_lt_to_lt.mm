$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_lt_to_lt (logipedia__metamath__nat.le_to_lt_to_lt), catalog title
  "nat.le_to_lt_to_lt": for all natural numbers n, m, and p, if n is less
  than or equal to m and m is less than p, then n is less than p. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native non-strict and strict orders
  represent nat.le and nat.lt; the latter is equivalent to the source
  definition nat.lt n m := nat.le (nat.S n) m. The three restricted universal
  quantifiers and nested implications preserve the source binder order,
  hypothesis order, conclusion, and all scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

logipedia-nat-le-to-lt-to-lt $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        (
          n <_ m
          ->
          (
            m < p
            ->
            n < p
          )
        )
$.
