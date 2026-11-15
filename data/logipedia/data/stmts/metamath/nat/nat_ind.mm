$(
  Statement-only formalization of the Logipedia corpus artifact nat.nat_ind
  (logipedia__metamath__nat.nat_ind), catalog title "nat.nat_ind": every
  predicate on natural numbers that holds at zero and is preserved by
  successor holds for every natural number. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain, with source zero nat.O represented by 0 and source
  successor nat.S n represented by n + 1. A source predicate
  Q : nat -> Prop is represented extensionally by an arbitrary subset p of
  NN0, so n e. p represents Q n. The restricted quantifiers and nested
  implications preserve the source binder order, scopes, assumptions, and
  conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d n p x $.

  logipedia-nat-nat-ind $a |-
    A. p e. ~P NN0
      (
        0 e. p
        ->
        (
          A. n e. NN0
            ( n e. p -> ( n + 1 ) e. p )
          ->
          A. x e. NN0 x e. p
        )
      )
  $.
$}
