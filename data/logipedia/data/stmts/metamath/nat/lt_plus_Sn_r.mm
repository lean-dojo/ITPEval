$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_plus_Sn_r (logipedia__metamath__nat.lt_plus_Sn_r), catalog title
  "nat.lt_plus_Sn_r": every natural number a is strictly less than
  (a + x) + (n + 1) for all natural numbers x and n. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's native addition and strict order represent
  nat.plus and nat.lt, and n + 1 represents the source successor nat.S n.
  The three restricted universal quantifiers preserve the source binder order
  and scopes. The final declaration is Metamath's native unproved $a statement
  encoding; this database contains no $p proof declaration.
$)

logipedia-nat-lt-plus-Sn-r $a |-
  A. a e. NN0
    A. x e. NN0
      A. n e. NN0
        ( a < ( ( a + x ) + ( n + 1 ) ) )
$.
