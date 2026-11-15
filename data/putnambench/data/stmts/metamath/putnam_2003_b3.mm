$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_b3: for every positive integer n, n factorial is the product
  from i = 1 through n of the least common multiple of the integers from
  1 through floor(n / i). This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P03B3LcmPrefix(k) is defined as the unique positive integer divisible by
  every member of 1 ... k and dividing every positive common multiple of
  that interval. This is exactly lcm{1,...,k}; when k = 0 both interval
  conditions characterize 1, matching the source fold initialized at 1.

  SetMM's |_ is the real floor function, 1 ... n is the inclusive positive
  integer interval, prod_ is finite product, and ! is factorial. Every
  declaration below is an unproved $a statement encoding, and this database
  contains no $p proof statement.
$)

$c P03B3LcmPrefix $.

p03b3-lcm-prefix-syntax $a class P03B3LcmPrefix $.

${
  $d j k m q $.

  p03b3-lcm-prefix-definition $a |- P03B3LcmPrefix =
    (
      k e. NN0 |->
        U. { m e. NN |
          (
            A. j e. ( 1 ... k ) j || m
            /\
            A. q e. NN
              (
                A. j e. ( 1 ... k ) j || q
                ->
                m || q
              )
          )
        }
    )
  $.
$}

${
  $d i n $.

  putnambench-putnam-2003-b3 $a |- A. n e. NN
    (
      ( ! ` n )
      =
      prod_ i e. ( 1 ... n )
        (
          P03B3LcmPrefix
          `
          ( |_ ` ( n / i ) )
        )
    )
  $.
$}
