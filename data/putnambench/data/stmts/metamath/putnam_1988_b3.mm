$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_b3: the least positive uniform upper bound for the minima of
  |c - d sqrt(3)| over nonnegative integers c,d with fixed positive sum is
  (1 + sqrt(3)) / 2. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions on the integers. For every
  positive integer n, the antecedent says both that F(n) is attained by some
  nonnegative integers c,d with c+d=n and that F(n) is no greater than every
  value from such a pair. Thus F(n) is exactly the source minimum r_n.

  The conclusion expands IsLeast for (1 + sqrt(3))/2: this number is positive,
  bounds every F(n), and is at most every other positive real uniform bound.
  Restricting n to NN and c,d to NN0 is equivalent to the source integer
  inequalities n>=1 and c,d>=0. Set.mm's principal square root and complex
  modulus agree with the real square root and real absolute value here.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F c d g n $.

  putnambench-putnam-1988-b3 $a |- A. F e. ( RR ^m ZZ )
    (
      A. n e. NN
        (
          (
            E. c e. NN0 E. d e. NN0
              (
                ( c + d ) = n
                /\
                ( F ` n )
                =
                ( abs ` ( c - ( d x. ( sqrt ` 3 ) ) ) )
              )
          )
          /\
          A. c e. NN0 A. d e. NN0
            (
              ( c + d ) = n
              ->
              ( F ` n )
              <_
              ( abs ` ( c - ( d x. ( sqrt ` 3 ) ) ) )
            )
        )
      ->
      (
        (
          0 < ( ( 1 + ( sqrt ` 3 ) ) / 2 )
          /\
          A. n e. NN
            ( F ` n ) <_ ( ( 1 + ( sqrt ` 3 ) ) / 2 )
        )
        /\
        A. g e. RR
          (
            (
              0 < g
              /\
              A. n e. NN ( F ` n ) <_ g
            )
            ->
            ( ( 1 + ( sqrt ` 3 ) ) / 2 ) <_ g
          )
      )
    )
  $.
$}
