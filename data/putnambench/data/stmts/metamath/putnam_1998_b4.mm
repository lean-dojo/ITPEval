$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_b4: positive integers for which the alternating sum determined
  by the two floor quotients vanishes, characterized by unequal exact powers
  of two dividing the integers. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN and NN0 are set.mm's positive and nonnegative integers. The half-open
  interval 0 ..^ (m*n) is exactly the source index range 0 <= i < m*n.
  Division is real division on these positive natural arguments, so applying
  the floor function reproduces the two source natural quotients.

  The internally existential r and s are the exact exponents of two in m and
  n: 2^r divides m but 2^(r+1) does not, and similarly for n. Their inequality
  is therefore exactly the annotated source condition that the two
  multiplicities differ. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d i m n r s $.

  putnambench-putnam-1998-b4 $a |-
    A. m e. NN
    A. n e. NN
      (
        (
          sum_ i e. ( 0 ..^ ( m x. n ) )
            (
              ( -u 1 )
              ^
              (
                ( |_ ` ( i / m ) )
                +
                ( |_ ` ( i / n ) )
              )
            )
        )
        =
        0
        <->
        E. r e. NN0
        E. s e. NN0
          (
            (
              ( 2 ^ r ) || m
              /\
              -. ( ( 2 ^ ( r + 1 ) ) || m )
            )
            /\
            (
              (
                ( 2 ^ s ) || n
                /\
                -. ( ( 2 ^ ( s + 1 ) ) || n )
              )
              /\
              r =/= s
            )
          )
      )
  $.
$}
