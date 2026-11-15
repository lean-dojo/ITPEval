$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_a5: evaluation of the real integral of the natural logarithm
  of x plus one divided by x squared plus one over the unit interval. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  Set.mm's S. binder is the real Lebesgue integral. The closed interval
  [0,1] agrees with the source interval integrals; endpoint inclusion does
  not change the integral. The standard SetMM constants log and _pi encode
  the natural logarithm and pi, so the right side is pi * log(2) / 8.

  The declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

putnambench-putnam-2005-a5 $a |- (
  S. ( 0 [,] 1 )
    (
      ( log ` ( x + 1 ) )
      /
      ( ( x ^ 2 ) + 1 )
    )
    _d x
  =
  (
    (
      _pi
      x.
      ( log ` 2 )
    )
    /
    8
  )
) $.
