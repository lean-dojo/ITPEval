$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_b5: the number of permutations of 1 through n that send
  adjacent positions to values at distance at most two satisfies a fixed
  integer recurrence with value four. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For each nonnegative integer n, P15B5Count is the finite cardinality of
  the permutations of the inclusive interval 1 ... n such that positions
  at distance one have image values at distance at most two. Base applied
  to SymGrp gives exactly the bijections of this interval, and integer
  absolute value expresses both distance conditions.

  The concluding arithmetic is ordinary subtraction and addition of the
  four natural cardinalities, hence is exactly the source expression after
  its casts to integers. The auxiliary declarations are syntax and the
  faithful counting-function definition; the final declaration is the
  single unproved $a corpus statement. This database contains no $p proof
  declaration.
$)

$c P15B5Count $.

p15b5-count-syntax $a class P15B5Count $.

${
  $d f i j n $.

  p15b5-count-definition $a |- P15B5Count =
    (
      n e. NN0 |->
        (
          #
          `
          {
            f e. ( Base ` ( SymGrp ` ( 1 ... n ) ) )
            |
            A. i e. ( 1 ... n )
              A. j e. ( 1 ... n )
                (
                  ( abs ` ( i - j ) ) = 1
                  ->
                  ( abs ` ( ( f ` i ) - ( f ` j ) ) ) <_ 2
                )
          }
        )
    )
  $.
$}

putnambench-putnam-2015-b5 $a |-
  A. n e. NN0
    (
      2 <_ n
      ->
      (
        (
          (
            (
              ( P15B5Count ` ( n + 5 ) )
              -
              ( P15B5Count ` ( n + 4 ) )
            )
            -
            ( P15B5Count ` ( n + 3 ) )
          )
          +
          ( P15B5Count ` n )
        )
      )
      =
      4
    )
$.
