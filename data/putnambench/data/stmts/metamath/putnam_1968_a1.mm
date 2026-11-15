$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1968_a1: the exact real identity relating 22/7 minus pi to the
  unit-interval integral of x^4(1-x)^4/(1+x^2). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The imported set.mm database supplies the standard real numbers, the real
  constant _pi, real arithmetic and powers, the closed interval [0,1], and
  the Lebesgue integral binder S. A F _d x. The displayed rational function
  is continuous on [0,1], so this integral is the same real interval integral
  used by all ground-truth sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

putnambench-putnam-1968-a1 $a |- (
  ( ( ; 2 2 / 7 ) - _pi )
  =
  S. ( 0 [,] 1 )
    (
      (
        ( x ^ 4 )
        x.
        ( ( 1 - x ) ^ 4 )
      )
      /
      ( 1 + ( x ^ 2 ) )
    )
    _d x
) $.
