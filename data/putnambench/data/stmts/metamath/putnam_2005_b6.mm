$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_b6: a signed reciprocal fixed-point sum over all permutations
  of a positive finite set. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN, the interval 1 ... n is an n-element carrier and the base of
  its symmetric group is exactly the set of all permutations of that carrier.
  SetMM's pmSgn is 1 on even permutations and -1 on odd permutations. The
  restricted class in the denominator is precisely the set of fixed points.
  Thus this is the source finite sum, with its rational values embedded in
  SetMM's number system.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d i n p $.

  putnambench-putnam-2005-b6 $a |- A. n e. NN
    (
      sum_ p e. ( Base ` ( SymGrp ` ( 1 ... n ) ) )
        (
          (
            ( pmSgn ` ( 1 ... n ) )
            `
            p
          )
          /
          (
            (
              #
              `
              {
                i e. ( 1 ... n )
                |
                ( p ` i ) = i
              }
            )
            +
            1
          )
        )
      =
      (
        ( -u 1 ^ ( n + 1 ) )
        x.
        ( n / ( n + 1 ) )
      )
    )
  $.
$}
