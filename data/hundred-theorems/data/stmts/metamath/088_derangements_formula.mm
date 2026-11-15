$(
  Statement-only formalization of "Derangements Formula" from the Hundred
  Theorems corpus artifact 088: the number of fixed-point-free permutations
  of a nonempty finite set is the nearest integer to the factorial of its
  cardinality divided by Euler's number. This file contains no proof.
$)

$[ library/set.mm $]

$(
  A derangement of A is represented directly as a bijection f from A onto A
  such that f(y) differs from y for every y in A. Thus the restricted class
  abstraction is exactly the set of fixed-point-free permutations of A.

  In set.mm, ! is the factorial function, _e is Euler's number, and
  |_ ` ( x + ( 1 / 2 ) ) is nearest-integer rounding for the value occurring
  here. The following declaration is an unproved $a assertion; this file has
  no $p proof statement.
$)

${
  $d A f $.  $d A y $.  $d f y $.

  hundred-theorems-088-derangements-formula $a
    |- ( ( A e. Fin /\ A =/= (/) ) ->
         ( # `
           { f |
             ( f : A -1-1-onto-> A /\
               A. y e. A ( f ` y ) =/= y )
           }
         ) =
         ( |_ ` ( ( ( ! ` ( # ` A ) ) / _e ) + ( 1 / 2 ) ) ) )
  $.
$}
