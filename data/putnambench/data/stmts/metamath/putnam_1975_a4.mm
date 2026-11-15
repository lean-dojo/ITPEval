$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1975_a4: evaluation of the reciprocal of one minus a primitive
  even-order complex root of unity as an integer polynomial in that root.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The variable m ranges over the nonnegative integers, and the hypotheses
  m mod 2 = 1 and 1 < m are exactly the source assumptions that m is odd
  and greater than one. The variable t is the source complex number theta,
  with its defining complex-exponential equality retained explicitly.

  The annotated source polynomial is the sum of the monomials X^(2j+1)
  for 0 <= j < (m-1)/2. Evaluating it at t gives the finite sum below.
  Since m is odd, (m-1)/2 is a nonnegative integer, so the half-open
  integer interval reproduces both source index ranges and all displayed
  coefficients are integers.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d j m t $.

  putnambench-putnam-1975-a4 $a |-
    A. m e. NN0 A. t e. CC
      (
        (
          (
            ( m mod 2 ) = 1
            /\
            1 < m
          )
          /\
          t =
            (
              exp
              `
              (
                ( ( 2 x. _pi ) x. _i )
                /
                ( 2 x. m )
              )
            )
        )
        ->
        (
          1
          /
          ( 1 - t )
        )
        =
        sum_ j e. ( 0 ..^ ( ( m - 1 ) / 2 ) )
          ( t ^ ( ( 2 x. j ) + 1 ) )
      )
  $.
$}
