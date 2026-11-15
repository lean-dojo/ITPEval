$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_a5: classification of the integers from 1 through 10 for which
  the integral from 0 to 2 pi of the product of cos(k x) for 1 <= k <= m is
  nonzero. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Set.mm's 1 ... m is the inclusive natural-number index interval, prod_ is
  its finite product, and S. is the real Lebesgue integral. Thus the left
  side of the biconditional is exactly I_m != 0 for the source integrand
  cos(x) cos(2x) ... cos(mx). The right side inlines the explicit solution
  predicate from the Rocq ground truth, equivalently the set {3, 4, 7, 8}
  identified by the other sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d k m x $.

  putnambench-putnam-1985-a5 $a |-
    A. m e. ( 1 ... ; 1 0 )
      (
        (
          S. ( 0 [,] ( 2 x. _pi ) )
            (
              prod_ k e. ( 1 ... m )
                ( cos ` ( k x. x ) )
            )
            _d x
        )
        =/=
        0
        <->
        (
          m = 3
          \/
          (
            m = 4
            \/
            (
              m = 7
              \/
              m = 8
            )
          )
        )
      )
  $.
$}
