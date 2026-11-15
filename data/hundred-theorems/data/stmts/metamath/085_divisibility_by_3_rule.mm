$(
  Statement-only formalization of "Divisibility by 3 Rule" from Hundred
  Theorems corpus artifact 085 (hundred-theorems__metamath__085): a finite
  base-10 expansion with integer coefficients is divisible by three exactly
  when the sum of its coefficients is divisible by three. This file contains
  no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library supplies nonnegative integers, integer-valued
  functions, inclusive finite intervals and sums, exponentiation, and integer
  divisibility. The coefficient function is arbitrary on 0 through N, so
  ordinary decimal digits are a special case. The final declaration is an
  unproved $a statement.
$)

${
  $d F k $.  $d N k $.

  hundred-theorems-085-divisibility-by-3 $a
    |- ( ( N e. NN0 /\ F : ( 0 ... N ) --> ZZ ) ->
         ( 3 || sum_ k e. ( 0 ... N )
                   ( ( F ` k ) x. ( ; 1 0 ^ k ) )
           <->
           3 || sum_ k e. ( 0 ... N ) ( F ` k ) ) )
  $.
$}
