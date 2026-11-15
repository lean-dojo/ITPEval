$(
  Statement-only formalization of "Formula for the Number of Combinations"
  from Hundred Theorems item 058: for every finite set and every nonnegative
  integer k, the family of its k-element subsets has cardinality equal to the
  corresponding binomial coefficient. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The free class variables are implicitly universally quantified.  The
  restricted power set expression denotes exactly the subsets of A having
  cardinality K.
$)
hundred-theorems-058-number-of-combinations $a
  |- ( ( A e. Fin /\ K e. NN0 ) ->
       ( # ` { x e. ~P A | ( # ` x ) = K } ) =
       ( ( # ` A ) _C K ) )
$.
