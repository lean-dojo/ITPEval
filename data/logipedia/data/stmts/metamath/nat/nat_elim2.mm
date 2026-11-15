$(
  Statement-only formalization of the Logipedia corpus artifact nat.nat_elim2
  (logipedia__metamath__nat.nat_elim2), catalog title "nat.nat_elim2":
  two-variable natural-number induction from the zero-row, positive
  zero-column, and simultaneous-successor cases. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain, with source zero nat.O represented by 0 and source
  successor nat.S n represented by n + 1. A source binary predicate
  R : nat -> nat -> Prop is represented extensionally by an arbitrary subset
  p of ( NN0 X. NN0 ), so <. n , m >. e. p represents R n m. The restricted
  quantifiers and nested implications preserve the source binder order,
  scopes, assumptions, and conclusion. The final declaration is Metamath's
  native unproved $a statement encoding; this artifact adds no $p proof
  declaration.
$)

${
  $d m n p $.

  logipedia-nat-nat-elim2 $a |-
    A. p e. ~P ( NN0 X. NN0 )
      (
        A. n e. NN0 <. 0 , n >. e. p
        ->
        (
          A. n e. NN0 <. ( n + 1 ) , 0 >. e. p
          ->
          (
            A. n e. NN0
              A. m e. NN0
                (
                  <. n , m >. e. p
                  ->
                  <. ( n + 1 ) , ( m + 1 ) >. e. p
                )
            ->
            A. n e. NN0
              A. m e. NN0 <. n , m >. e. p
          )
        )
      )
  $.
$}
