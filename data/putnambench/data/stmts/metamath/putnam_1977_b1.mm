$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_b1: the real infinite product of (n^3 - 1) / (n^3 + 1)
  from n = 2 onward converges to 2 / 3. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, the finite product is over the inclusive integer interval
  from 2 through n. Thus the NN0-indexed expression is the sequence of
  partial products of the source infinite product. Its values at n = 0 and
  n = 1 are empty products, which do not affect convergence and match the
  leading unit factors in the Rocq source.

  The target 2 / 3 is the explicit solution in the Rocq source and the
  solution annotation in the Lean and Isabelle sources. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d i n $.

  putnambench-putnam-1977-b1 $a |-
    (
      n e. NN0 |->
        prod_ i e. ( 2 ... n )
          (
            ( ( i ^ 3 ) - 1 )
            /
            ( ( i ^ 3 ) + 1 )
          )
    )
    ~~>
    ( 2 / 3 )
  $.
$}
