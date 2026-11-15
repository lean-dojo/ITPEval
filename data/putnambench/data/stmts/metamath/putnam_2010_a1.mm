$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_a1: the largest number of boxes into which the integers from
  one through a positive n can be placed with equal box sums is the
  specified natural-valued solution. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P2010A1Solution is the resolved function floor((n+1)/2), equivalently
  ceil(n/2) on natural n. P2010A1Feasible n k says that there is a
  total assignment of the integers 1 through n to the k-element ordinal
  0 ..^ k such that every two fibers have the same sum.

  The source predicate kboxes is eliminated using its defining equivalence.
  The final conjunction expands IsGreatest: the specified solution value is
  feasible, and every feasible natural k is at most that value. Thus this is
  a bidirectionally equivalent rendering of the source theorem. All
  declarations are unproved $a statement encodings; there is no $p proof.
$)

$c P2010A1Solution P2010A1Feasible $.

p2010a1-solution-syntax $a class P2010A1Solution $.
p2010a1-feasible-syntax $a wff ( P2010A1Feasible A B ) $.

p2010a1-solution-definition $a |- P2010A1Solution =
  ( n e. NN0 |-> ( |_ ` ( ( n + 1 ) / 2 ) ) ) $.

${
  $d A B b i j x $.

  p2010a1-feasible-definition $a |- (
    ( P2010A1Feasible A B )
    <->
    E. b e. ( ( 0 ..^ B ) ^m ( 1 ... A ) )
      A. i e. ( 0 ..^ B )
        A. j e. ( 0 ..^ B )
          (
            sum_ x e. { x e. ( 1 ... A ) | ( b ` x ) = i } x
            =
            sum_ x e. { x e. ( 1 ... A ) | ( b ` x ) = j } x
          )
  ) $.
$}

${
  $d k n $.

  putnambench-putnam-2010-a1 $a |- A. n e. NN
    (
      ( P2010A1Feasible n ( P2010A1Solution ` n ) )
      /\
      A. k e. NN0
        (
          ( P2010A1Feasible n k )
          ->
          k <_ ( P2010A1Solution ` n )
        )
    )
  $.
$}
