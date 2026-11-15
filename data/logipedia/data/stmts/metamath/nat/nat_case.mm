$(
  Statement-only formalization of the Logipedia corpus artifact nat.nat_case
  (logipedia__metamath__nat.nat_case), catalog title "nat.nat_case":
  natural-number case analysis derives an arbitrary predicate at a natural
  number from its zero and successor cases. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain, with source zero nat.O represented by 0 and source
  successor nat.S m represented by m + 1. A source predicate
  P : nat -> Prop is represented extensionally by an arbitrary subset p of
  NN0, so x e. p represents P x. SetMM's native equality on NN0 represents
  the source natural-number equality. The restricted quantifiers and nested
  implications preserve the source binder order, scopes, assumptions, and
  conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d m n p $.

  logipedia-nat-nat-case $a |-
    A. n e. NN0
      A. p e. ~P NN0
        (
          ( n = 0 -> 0 e. p )
          ->
          (
            A. m e. NN0
              ( n = ( m + 1 ) -> ( m + 1 ) e. p )
            ->
            n e. p
          )
        )
  $.
$}
