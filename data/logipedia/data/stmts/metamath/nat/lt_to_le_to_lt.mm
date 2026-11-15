$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_to_le_to_lt (logipedia__metamath__nat.lt_to_le_to_lt), catalog title
  "nat.lt_to_le_to_lt": for all natural numbers n, m, and p, if n is less
  than m and m is less than or equal to p, then n is less than p. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. On NN0, SetMM's native strict and non-strict orders
  represent nat.lt and nat.le; the strict order is equivalent to the source
  definition nat.lt n m := nat.le (nat.S n) m. The three restricted universal
  quantifiers and nested implications preserve the source binder order,
  hypothesis order, conclusion, and all scopes. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

logipedia-nat-lt-to-le-to-lt $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        (
          n < m
          ->
          (
            m <_ p
            ->
            n < p
          )
        )
$.
