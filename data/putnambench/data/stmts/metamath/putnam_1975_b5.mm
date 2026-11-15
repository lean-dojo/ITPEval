$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_b5: the factorial-weighted infinite sum at one of the recursively
  defined functions f_0(x) = exp(x) and f_(n+1)(x) = x f_n'(x) equals
  exp(exp(1)). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all NN0-indexed families of total real-valued functions.
  P75B5Deriv totalizes set.mm's partial real derivative by assigning zero
  where the derivative does not exist, matching the total derivative
  convention of the source formalizations.

  The sum over NN0 is set.mm's convergent infinite real-series sum. The
  factorial, evaluation at one, recurrence, and nested exponential are
  retained directly. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

$c P75B5Deriv $.

p75b5-deriv-syntax $a class ( P75B5Deriv A ) $.

${
  $d A x $.

  p75b5-deriv-definition $a |- ( P75B5Deriv A ) =
    (
      x e. RR |->
        if (
          x e. dom ( RR _D A ) ,
          ( ( RR _D A ) ` x ) ,
          0
        )
    )
  $.
$}

${
  $d F n x $.

  putnambench-putnam-1975-b5 $a |- A. F e.
    ( ( RR ^m RR ) ^m NN0 )
    (
      (
        A. x e. RR
          ( ( F ` 0 ) ` x ) = ( exp ` x )
        /\
        A. n e. NN0 A. x e. RR
          ( ( F ` ( n + 1 ) ) ` x )
          =
          (
            x
            x.
            ( ( P75B5Deriv ( F ` n ) ) ` x )
          )
      )
      ->
      (
        sum_ n e. NN0
          (
            ( ( F ` n ) ` 1 )
            /
            ( ! ` n )
          )
      )
      =
      ( exp ` ( exp ` 1 ) )
    )
  $.
$}
