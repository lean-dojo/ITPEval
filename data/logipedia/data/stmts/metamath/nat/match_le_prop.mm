$(
  Statement-only formalization of the Logipedia corpus artifact
  nat.match_le_prop (logipedia__metamath__nat.match_le_prop), catalog title
  "nat.match_le_prop": a predicate holding at a natural lower bound and at
  every successor holds at every natural number above that bound. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. A source predicate return_ : nat -> Prop is
  represented extensionally by an arbitrary subset p of NN0, so m e. p
  represents return_ m. SetMM's native non-strict order on NN0 represents
  nat.le, and m + 1 represents the source successor nat.S m. The restricted
  quantifiers and nested implications preserve the source binder order,
  assumptions, scopes, and conclusion. The final declaration is Metamath's
  native unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

${
  $d m n p $.

  logipedia-nat-match-le-prop $a |-
    A. n e. NN0
      A. p e. ~P NN0
        (
          n e. p
          ->
          (
            A. m e. NN0 ( m + 1 ) e. p
            ->
            A. m e. NN0
              ( n <_ m -> m e. p )
          )
        )
  $.
$}
