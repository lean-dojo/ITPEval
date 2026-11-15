$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_to_le_to_lt_times
  (logipedia__metamath__nat.lt_to_le_to_lt_times), catalog title
  "nat.lt_to_le_to_lt_times": for natural numbers n, m, p, and q, strict
  increase from n to m, non-strict increase from p to q, and positivity of q
  imply that n times p is strictly less than m times q. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's total multiplication and native strict and
  non-strict orders represent nat.times, nat.lt, and nat.le; 0 represents
  nat.O. The four restricted universal quantifiers and three nested
  implications preserve the source binder order, hypothesis order, conclusion,
  and all scopes. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

logipedia-nat-lt-to-le-to-lt-times $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. NN0
        A. q e. NN0
          (
            n < m
            ->
            (
              p <_ q
              ->
              (
                0 < q
                ->
                ( n x. p ) < ( m x. q )
              )
            )
          )
$.
