$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2013_a3: a vanishing finite sum of real coefficients divided by
  one minus successive powers of a point in the open unit interval implies
  that the associated real polynomial has a root in that interval. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN0, the interval 0 ... n is exactly the source index set from
  zero through n, and RR ^m ( 0 ... n ) is the class of all real coefficient
  families on that finite carrier. Thus both finite sums use precisely the
  coefficients a_0 through a_n.

  The antecedent preserves 0 < x < 1 and the vanishing sum with denominator
  1 - x^(i+1). The witness y remains existentially quantified inside the
  conclusion, with 0 < y < 1 and the associated polynomial sum equal to zero.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d a i n x y $.

  putnambench-putnam-2013-a3 $a |-
    A. n e. NN0
      A. a e. ( RR ^m ( 0 ... n ) )
        A. x e. RR
          (
            (
              (
                0 < x
                /\
                x < 1
              )
              /\
              (
                sum_ i e. ( 0 ... n )
                  (
                    ( a ` i )
                    /
                    (
                      1
                      -
                      ( x ^ ( i + 1 ) )
                    )
                  )
              )
              =
              0
            )
            ->
            E. y e. RR
              (
                (
                  0 < y
                  /\
                  y < 1
                )
                /\
                (
                  sum_ i e. ( 0 ... n )
                    (
                      ( a ` i )
                      x.
                      ( y ^ i )
                    )
                )
                =
                0
              )
          )
  $.
$}
