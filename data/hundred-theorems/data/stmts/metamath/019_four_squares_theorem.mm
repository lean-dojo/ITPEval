$(
  Statement-only formalization of "Four Squares Theorem" from Hundred Theorems item 019:
  every natural number is a sum of four squares of natural numbers. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library supplies the standard class NN0 of nonnegative
  integers, used here as the natural numbers, together with standard equality,
  addition, exponentiation, and the numeral 2. The final declaration is an
  unproved $a statement.
$)

hundred-theorems-019-four-squares $a
  |- A. n e. NN0
       E. a e. NN0
         E. b e. NN0
           E. c e. NN0
             E. d e. NN0
               n = ( ( ( a ^ 2 ) + ( b ^ 2 ) ) + ( c ^ 2 ) ) + ( d ^ 2 )
$.
