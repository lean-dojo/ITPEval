$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_n_O_elim (logipedia__metamath__nat.le_n_O_elim), catalog title
  "nat.le_n_O_elim": a natural number below or equal to zero satisfies every
  predicate that holds at zero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O, and its native
  non-strict order on NN0 represents nat.le. A source predicate
  P : nat -> Prop is represented extensionally by an arbitrary subset p of
  NN0, so x e. p represents P x. The restricted quantifiers and nested
  implications preserve the source binder order, scopes, assumption, and
  conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this artifact adds no $p proof declaration.
$)

${
  $d n p $.

  logipedia-nat-le-n-O-elim $a |-
    A. n e. NN0
      (
        n <_ 0
        ->
        A. p e. ~P NN0
          ( 0 e. p -> n e. p )
      )
  $.
$}
