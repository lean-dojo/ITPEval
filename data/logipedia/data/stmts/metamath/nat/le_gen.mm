$(
  Statement-only formalization of the Logipedia corpus artifact nat.le_gen
  (logipedia__metamath__nat.le_gen), catalog title "nat.le_gen": for every
  predicate on natural numbers and every natural number n, if the predicate
  holds for each natural number at most n, then it holds for n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. A source predicate P : nat -> Prop is represented
  extensionally by an arbitrary subset p of NN0, so i e. p represents P i.
  SetMM's native non-strict order on NN0 represents nat.le. The restricted
  quantifiers and implication preserve the source binder order and scopes.
  The final declaration is Metamath's native unproved $a statement encoding;
  this artifact adds no $p proof declaration.
$)

${
  $d i n p $.

  logipedia-nat-le-gen $a |-
    A. p e. ~P NN0
      A. n e. NN0
        (
          A. i e. NN0
            ( i <_ n -> i e. p )
          ->
          n e. p
        )
  $.
$}
