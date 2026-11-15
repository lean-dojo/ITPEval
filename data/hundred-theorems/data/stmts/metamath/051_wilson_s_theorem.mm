$(
  Statement-only formalization of "Wilson's Theorem" from Hundred Theorems
  item 051: for every natural number other than one, primality is equivalent
  to the Wilson factorial congruence modulo that number. This file contains
  no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library supplies the standard classes NN0 and NN, the
  class Prime, factorial, integer subtraction, unary negation, modulo, and
  restricted quantification.

  The source statements quantify over natural n with n =/= 1. At n = 0 their
  natural-number factorial congruence is false. The conjunct n e. NN records
  that zero case explicitly; for every remaining n, set.mm subtraction agrees
  with natural-number subtraction, and equality of the displayed remainders
  says exactly that (n - 1)! is congruent to -1 modulo n.

  The final declaration is an unproved $a statement and introduces no $p
  proof.
$)

hundred-theorems-051-wilson $a
  |- A. n e. NN0
       (
         n =/= 1
         ->
         (
           n e. Prime
           <->
           (
             n e. NN
             /\
             ( ( ! ` ( n - 1 ) ) mod n ) = ( -u 1 mod n )
           )
         )
       )
$.
