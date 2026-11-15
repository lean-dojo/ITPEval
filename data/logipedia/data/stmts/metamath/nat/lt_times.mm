$(
  Statement-only formalization of the Logipedia corpus artifact nat.lt_times
  (logipedia__metamath__nat.lt_times), catalog title "nat.lt_times":
  multiplication on natural numbers preserves strict order when both
  arguments strictly increase. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total multiplication and native strict order
  represent nat.times and nat.lt. The four restricted universal quantifiers
  and nested implications preserve the source binder order, scopes, two
  assumptions, and conclusion. The final declaration is Metamath's native
  unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

logipedia-nat-lt-times $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        A. q e. NN0
          (
            n < m
            ->
            (
              p < q
              ->
              ( n x. p ) < ( m x. q )
            )
          )
$.
