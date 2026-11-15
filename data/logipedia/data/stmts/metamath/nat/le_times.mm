$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_times
  (logipedia__metamath__nat.le_times), catalog title "nat.le_times":
  multiplication on natural numbers preserves non-strict order in both
  arguments. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total multiplication and native non-strict
  order represent nat.times and nat.le. Source variables n1, n2, m1, and m2
  are alpha-renamed to n, m, p, and q. The four restricted universal
  quantifiers and nested implications preserve the source binder order,
  scopes, two assumptions, and conclusion. The final declaration is
  Metamath's native unproved $a statement encoding; this database contains no
  $p proof declaration.
$)

logipedia-nat-le-times $a |-
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
              ( n x. p ) <_ ( m x. q )
            )
          )
$.
