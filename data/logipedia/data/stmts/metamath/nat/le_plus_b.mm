$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_plus_b
  (logipedia__metamath__nat.le_plus_b), catalog title "nat.le_plus_b": if
  adding a natural number b to n gives a value at most m, then n is at most
  m. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native non-strict order
  represent nat.plus and nat.le. The three restricted universal quantifiers
  preserve the source binder order b, n, m and their scopes; the implication
  preserves the sole assumption and conclusion. The final declaration is
  Metamath's native unproved $a statement encoding; this artifact adds no $p
  proof declaration.
$)

logipedia-nat-le-plus-b $a |-
  A. b e. NN0
    A. n e. NN0
      A. m e. NN0
        ( ( n + b ) <_ m -> n <_ m )
$.
