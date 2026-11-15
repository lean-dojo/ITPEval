$(
  Statement-only formalization of "The Principle of Mathematical Induction"
  from Hundred Theorems corpus artifact 074: every predicate on the
  nonnegative natural numbers that holds at zero and is preserved by
  successor holds for every nonnegative natural number. This file contains no
  proof.
$)

$[ library/set.mm $]

$(
  The predicate is represented extensionally by the set p: n e. p means that
  the predicate holds at n. The following is an unproved statement assertion.
$)
hundred-theorems-074-mathematical-induction $a
  |- A. p
      ( ( 0 e. p /\ A. n e. NN0 ( n e. p -> ( n + 1 ) e. p ) )
        -> A. n e. NN0 n e. p ) $.
