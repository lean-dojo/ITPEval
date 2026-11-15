$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_plus
  (logipedia__metamath__nat.le_plus), catalog title "nat.le_plus": addition
  on natural numbers preserves non-strict order in both arguments. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total addition and native non-strict order
  represent nat.plus and nat.le. Source variables n1, n2, m1, and m2 are
  alpha-renamed to n, m, p, and q. The four restricted universal quantifiers
  and nested implications preserve the source binder order, scopes, two
  assumptions, and conclusion. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

logipedia-nat-le-plus $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        A. q e. NN0
          (
            n <_ m
            ->
            (
              p <_ q
              ->
              ( n + p ) <_ ( m + q )
            )
          )
$.
