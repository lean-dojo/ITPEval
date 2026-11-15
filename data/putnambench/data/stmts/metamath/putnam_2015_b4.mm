$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2015_b4: the sum of 2^a / (3^b 5^c) over positive-integer
  triples that are side lengths of a triangle is the reduced rational
  number 17 / 21. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN is the class of positive integers. The three strict
  inequalities are exactly the triangle conditions for positive side
  lengths a, b, and c. Each sum_ is an infinite series over positive
  integers; nesting them is equivalent to summing over all admissible
  triples because every displayed term is nonnegative.

  The equality to 17 / 21 directly states the requested rational value in
  lowest terms. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d a b c $.

  putnambench-putnam-2015-b4 $a |-
    (
      sum_ a e. NN
        sum_ b e. NN
          sum_ c e.
            {
              c e. NN
              |
              (
                a < ( b + c )
                /\
                (
                  b < ( c + a )
                  /\
                  c < ( a + b )
                )
              )
            }
            (
              ( 2 ^ a )
              /
              (
                ( 3 ^ b )
                x.
                ( 5 ^ c )
              )
            )
    )
    =
    ( ; 1 7 / ; 2 1 )
  $.
$}
