$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_ind
  (logipedia__metamath__nat.le_ind), catalog title "nat.le_ind": induction
  above an arbitrary natural-number lower bound for predicates closed under
  successor. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. A source predicate Q : nat -> Prop is represented
  extensionally by an arbitrary subset p of NN0, so m e. p represents Q m.
  SetMM's native non-strict order on NN0 represents nat.le, and m + 1
  represents the source successor nat.S m. The restricted quantifiers and
  nested implications preserve the source binder order, scopes, assumptions,
  and conclusion. The final declaration is Metamath's native unproved $a
  statement encoding; this database contains no $p proof declaration.
$)

${
  $d m n p $.

  logipedia-nat-le-ind $a |-
    A. n e. NN0
      A. p e. ~P NN0
        (
          n e. p
          ->
          (
            A. m e. NN0
              (
                n <_ m
                ->
                ( m e. p -> ( m + 1 ) e. p )
              )
            ->
            A. m e. NN0
              ( n <_ m -> m e. p )
          )
        )
  $.
$}
