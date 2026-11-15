$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2017_b3: irrationality at one half for a zero-one coefficient
  power series whose value at two thirds is three halves. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is SetMM's class of all real-valued sequences indexed by the
  nonnegative integers. The restricted universal quantifier retains the
  condition that every coefficient is zero or one.

  Each unbounded sum_ is SetMM's infinite-series sum. The antecedent states
  that the series at 2/3 converges to 3/2. Membership of the series at 1/2 in
  RR \ QQ states both that it converges to a real value and that this value
  is irrational. Eliminating the source function f by its defining
  power-series equality is a definitional reformulation.

  The final declaration is the single unproved $a corpus statement.
$)

${
  $d c n $.

  putnambench-putnam-2017-b3 $a |-
    A. c e. ( RR ^m NN0 )
      (
        (
          (
            A. n e. NN0
              (
                ( c ` n ) = 0
                \/
                ( c ` n ) = 1
              )
          )
          /\
          (
            sum_ n e. NN0
              (
                ( c ` n )
                x.
                ( ( 2 / 3 ) ^ n )
              )
          )
          =
          ( 3 / 2 )
        )
        ->
        (
          sum_ n e. NN0
            (
              ( c ` n )
              x.
              ( ( 1 / 2 ) ^ n )
            )
        )
        e.
        ( RR \ QQ )
      )
  $.
$}
