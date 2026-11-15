$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2006_b6: a positive real sequence defined by adding the reciprocal
  k-th root of its current term has a specified normalized power limit.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The variable k ranges over the nonnegative integers, with the source
  hypothesis 1 < k, and a ranges over all NN0-indexed real sequences.
  For positive real bases, SetMM's complex power with exponent 1 / k is the
  positive real k-th root, so the recurrence is the source recurrence.

  The relation ~~> is SetMM's sequence convergence relation. Its right-hand
  side is the closed form ((k + 1) / k)^k supplied by the Putnam problem and
  the Rocq reference. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d a k n $.

  putnambench-putnam-2006-b6 $a |- A. k e. NN0
    (
      1 < k
      ->
      A. a e. ( RR ^m NN0 )
        (
          (
            0 < ( a ` 0 )
            /\
            A. n e. NN0
              ( a ` ( n + 1 ) )
              =
              (
                ( a ` n )
                +
                (
                  1
                  /
                  ( ( a ` n ) ^c ( 1 / k ) )
                )
              )
          )
          ->
          (
            n e. NN0 |->
              (
                ( ( a ` n ) ^ ( k + 1 ) )
                /
                ( n ^ k )
              )
          )
          ~~>
          ( ( ( k + 1 ) / k ) ^ k )
        )
    )
  $.
$}
