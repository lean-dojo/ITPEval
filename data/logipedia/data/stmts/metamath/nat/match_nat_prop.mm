$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.match_nat_prop (logipedia__metamath__nat.match_nat_prop), catalog title
  "nat.match_nat_prop": natural-number proposition elimination, where a
  predicate holding at zero and at every successor holds at every natural
  number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain, with source zero nat.O represented by 0 and source
  successor nat.S n represented by n + 1. A source predicate
  return_ : nat -> Prop is represented extensionally by an arbitrary subset p
  of NN0, so z e. p represents return_ z. The restricted quantifiers and
  nested implications preserve the source binder order, scopes, assumptions,
  and conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d n p z $.

  logipedia-nat-match-nat-prop $a |-
    A. p e. ~P NN0
      (
        0 e. p
        ->
        (
          A. n e. NN0 ( n + 1 ) e. p
          ->
          A. z e. NN0 z e. p
        )
      )
  $.
$}
