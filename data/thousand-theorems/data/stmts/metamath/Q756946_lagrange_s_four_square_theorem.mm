$(
  Statement-only formalization of Thousand Theorems corpus artifact Q756946
  (thousand-theorems__metamath__Q756946), "Lagrange's four-square theorem":
  every natural number is a sum of four squares of natural numbers. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The included set.mm library supplies NN0, the standard class of nonnegative
  integers used here for the source natural-number domain, together with
  equality, addition, exponentiation, and the numeral 2. The nested restricted
  existential quantifiers keep all four witnesses internal to the statement.

  The final $a declaration is the single unproved corpus statement; there is
  no $p proof statement.
$)

thousand-theorems-q756946-lagrange-four-square $a
  |- A. n e. NN0
       E. a e. NN0
         E. b e. NN0
           E. c e. NN0
             E. d e. NN0
               ( ( ( a ^ 2 ) + ( b ^ 2 ) ) + ( c ^ 2 ) ) + ( d ^ 2 ) = n
$.
