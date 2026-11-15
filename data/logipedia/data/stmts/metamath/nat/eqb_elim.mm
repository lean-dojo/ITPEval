$(
  Statement-only formalization of the Logipedia corpus artifact nat.eqb_elim
  (logipedia__metamath__nat.eqb_elim), catalog title "nat.eqb_elim":
  elimination for Boolean equality on natural numbers, where predicates at
  the true and false equality cases determine the predicate at eqb. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers and represents the source
  natural-number domain. The source Boolean carrier is represented exactly by
  { 0 , 1 }, with true represented by 1 and false by 0. A predicate
  P : bool -> Prop is represented extensionally by a subset p of this carrier,
  so b e. p means P b. The conditional if ( n = m , 1 , 0 ) is the source
  Boolean equality test nat.eqb n m. The restricted quantifiers and nested
  implications preserve the source binder order, assumptions, and conclusion.
  The final $a declaration is Metamath's native unproved statement encoding;
  this artifact adds no $p proof declaration.
$)

logipedia-nat-eqb-elim $a |-
  A. n e. NN0
    A. m e. NN0
      A. p e. ~P { 0 , 1 }
        (
          ( n = m -> 1 e. p )
          ->
          (
            ( -. n = m -> 0 e. p )
            ->
            if ( n = m , 1 , 0 ) e. p
          )
        )
$.
