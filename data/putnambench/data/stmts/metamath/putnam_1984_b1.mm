$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1984_b1: the factorial partial-sum function satisfies the recurrence
  with P(x) = x + 3 and Q(x) = -x - 2 at every positive integer index.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  ZZ ^m NN0 is the class of all integer-valued functions on the nonnegative
  integers, NN is the class of positive integers, and ! is factorial. Thus
  the antecedent is exactly f(n) = 1! + ... + n! for every positive n.

  The source polynomials are fixed by the ground-truth solution annotations
  and the explicit Rocq definition. Their evaluations are inlined as n + 3
  and (-n) - 2, respectively, which is definitionally equivalent to applying
  P(x) = x + 3 and Q(x) = -x - 2. The final declaration is the single
  unproved $a corpus statement; this root file declares no $p proof statement.
$)

${
  $d f i n $.

  putnambench-putnam-1984-b1 $a |- A. f e. ( ZZ ^m NN0 )
    (
      A. n e. NN
        (
          ( f ` n )
          =
          sum_ i e. ( 1 ... n ) ( ! ` i )
        )
      ->
      A. n e. NN
        (
          ( f ` ( n + 2 ) )
          =
          (
            ( ( n + 3 ) x. ( f ` ( n + 1 ) ) )
            +
            ( ( ( -u n ) - 2 ) x. ( f ` n ) )
          )
        )
    )
  $.
$}
