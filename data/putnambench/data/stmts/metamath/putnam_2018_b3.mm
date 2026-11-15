$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_b3: the positive integers below 10^100 satisfying three
  divisibility conditions involving 2^n are exactly 2^2, 2^4, 2^16, and
  2^256. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is SetMM's class of positive integers, and || is integer divisibility.
  Thus the subtractions n - 1, n - 2, 2^n - 1, and 2^n - 2 are interpreted
  in integer arithmetic, matching the Lean statement's integer coercions.
  The biconditional explicitly identifies every and only solution, as in the
  published problem and the Rocq solution predicate.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  putnambench-putnam-2018-b3 $a |- A. n e. NN
    (
      (
        n < ( ; 1 0 ^ ; ; 1 0 0 )
        /\
        (
          n || ( 2 ^ n )
          /\
          (
            ( n - 1 ) || ( ( 2 ^ n ) - 1 )
            /\
            ( n - 2 ) || ( ( 2 ^ n ) - 2 )
          )
        )
      )
      <->
      (
        n = ( 2 ^ 2 )
        \/
        (
          n = ( 2 ^ 4 )
          \/
          (
            n = ( 2 ^ ; 1 6 )
            \/
            n = ( 2 ^ ; ; 2 5 6 )
          )
        )
      )
    )
  $.
$}
