$(
  Statement-only formalization of Hundred Theorems corpus artifact 098
  (hundred-theorems__metamath__098), "Bertrand's Postulate": every positive
  natural number is strictly below a prime that is at most twice that number.
  This file contains no proof.
$)

$[ library/set.mm $]

$(
  NN is the set.mm class of positive integers and Prime is its class of prime
  natural numbers. For the Isabelle and Rocq formulations, which assume
  n >= 2, the displayed upper bound is equivalently strict: 2 times n is then
  composite and cannot equal p. Their omitted n = 1 case has p = 2. The
  assertion also implies the HOL Light formulation with the non-strict lower
  bound. The final declaration is an unproved $a statement.
$)

${
  $d n p $.

  hundred-theorems-098-bertrand-postulate $a
    |- A. n e. NN
         E. p e. Prime
           ( n < p /\ p <_ ( 2 x. n ) )
  $.
$}
