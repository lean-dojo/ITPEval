$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_b6: evaluation of the alternating series whose coefficient at
  each positive integer counts its odd divisors below sqrt(2k). This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and NN are SetMM's nonnegative and positive integers. Thus A ranges
  over the same natural-valued sequences as in the sources, while its
  defining equation is required exactly at the positive indices used by the
  series. The class

    { j e. NN | ( j e. Odd /\ ( j || k /\ j < ( sqrt ` ( 2 x. k ) ) ) ) }

  is precisely the finite set of odd positive divisors of k in
  [1,sqrt(2k)); its finite cardinality therefore matches the source encard.
  The unbounded sum_ binder is the real infinite series, and _pi is SetMM's
  real constant pi. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d A j k $.

  putnambench-putnam-2015-b6 $a |-
    A. A
      (
        (
          A : NN0 --> NN0
          /\
          A. k e. NN
            ( A ` k )
            =
            (
              #
              `
              {
                j e. NN |
                (
                  j e. Odd
                  /\
                  (
                    j || k
                    /\
                    j < ( sqrt ` ( 2 x. k ) )
                  )
                )
              }
            )
        )
        ->
        (
          sum_ k e. NN
            (
              ( ( -u 1 ) ^ ( k - 1 ) )
              x.
              ( ( A ` k ) / k )
            )
        )
        =
        ( ( _pi ^ 2 ) / ( ; 1 6 ) )
      )
  $.
$}
