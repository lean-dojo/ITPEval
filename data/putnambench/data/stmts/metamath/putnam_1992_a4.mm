$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1992_a4: determination of every positive-order derivative at zero
  of a smooth real function prescribed at the reciprocal positive integers.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is set.mm's class of total real-valued functions on the reals.
  Membership in the intersection of the range of ( C^n ` RR ) states that
  the function is continuously differentiable to every nonnegative order.
  The class ( RR Dn F ) is its sequence of iterated real derivatives.

  Quantifying n and k over NN is equivalent to the source restrictions
  n > 0 and k > 0. Divisibility of k by two selects the even derivative
  formula (-1)^(k/2) k!; the odd derivatives are zero. The final declaration
  is the single unproved $a corpus statement; this database contains no $p
  proof statement.
$)

${
  $d F k n $.

  putnambench-putnam-1992-a4 $a |- A. F e. ( RR ^m RR )
    (
      (
        F e. |^| ran ( C^n ` RR )
        /\
        A. n e. NN
          ( F ` ( 1 / n ) )
          =
          (
            ( n ^ 2 )
            /
            ( ( n ^ 2 ) + 1 )
          )
      )
      ->
      A. k e. NN
        ( ( ( RR Dn F ) ` k ) ` 0 )
        =
        if (
          2 || k ,
          (
            ( ( -u 1 ) ^ ( k / 2 ) )
            x.
            ( ! ` k )
          ) ,
          0
        )
    )
  $.
$}
