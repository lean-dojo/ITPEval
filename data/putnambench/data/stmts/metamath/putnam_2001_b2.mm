$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2001_b2: the real solutions of a two-equation reciprocal and
  quartic system form one explicit pair involving the fifth root of three.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The variables x and y range over all real numbers. The source hypotheses
  x != 0 and y != 0 remain explicit, and both source equations occur together
  on the left side of the biconditional.

  Since 3 is positive and 1 / 5 is real, set.mm's complex-power expression
  3 ^c ( 1 / 5 ) is the positive real fifth root used by the source
  solution. The final declaration is the single unproved $a corpus statement;
  this root file declares no $p proof statement.
$)

${
  $d x y $.

  putnambench-putnam-2001-b2 $a |-
    A. x e. RR A. y e. RR
      (
        (
          x =/= 0
          /\
          y =/= 0
        )
        ->
        (
          (
            (
              ( ( 1 / x ) + ( 1 / ( 2 x. y ) ) )
              =
              (
                ( ( x ^ 2 ) + ( 3 x. ( y ^ 2 ) ) )
                x.
                ( ( 3 x. ( x ^ 2 ) ) + ( y ^ 2 ) )
              )
            )
            /\
            (
              ( ( 1 / x ) - ( 1 / ( 2 x. y ) ) )
              =
              ( 2 x. ( ( y ^ 4 ) - ( x ^ 4 ) ) )
            )
          )
          <->
          (
            x = ( ( ( 3 ^c ( 1 / 5 ) ) + 1 ) / 2 )
            /\
            y = ( ( ( 3 ^c ( 1 / 5 ) ) - 1 ) / 2 )
          )
        )
      )
  $.
$}
