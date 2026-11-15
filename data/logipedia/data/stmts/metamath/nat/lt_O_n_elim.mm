$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.lt_O_n_elim (logipedia__metamath__nat.lt_O_n_elim), catalog title
  "nat.lt_O_n_elim": a positive natural number satisfies every predicate
  that holds of all successors. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. SetMM's 0 represents nat.O, n + 1 represents the
  source successor nat.S n, and its native strict order on NN0 represents
  nat.lt. A source predicate P : nat -> Prop is represented extensionally by
  an arbitrary subset p of NN0, so x e. p represents P x. The restricted
  quantifiers and nested implications preserve the source binder order,
  scopes, assumptions, and conclusion. The final declaration is Metamath's
  native unproved $a statement encoding; this artifact adds no $p proof
  declaration.
$)

${
  $d m n p $.

  logipedia-nat-lt-O-n-elim $a |-
    A. n e. NN0
      (
        0 < n
        ->
        A. p e. ~P NN0
          (
            A. m e. NN0
              ( ( m + 1 ) e. p )
            ->
            n e. p
          )
      )
  $.
$}
