$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1997_a5: the number of ordered 10-tuples of positive integers
  whose reciprocal sum is one is odd. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The half-open ordinal interval 0 ..^ 10 is the ten-element carrier
  corresponding to Fin 10, and NN ^m (0 ..^ 10) is the class of all ordered
  positive-integer 10-tuples. The restricted class retains exactly those
  tuples whose finite real reciprocal sum is one. SetMM's # operator gives
  its finite cardinality, and Odd is the class of odd integers.

  The source solution proposition is True, so the final declaration states
  the oddness conclusion directly. It is a single unproved $a corpus
  statement; this database contains no $p proof declaration.
$)

${
  $d i t $.

  putnambench-putnam-1997-a5 $a |-
    (
      #
      `
      {
        t e. ( NN ^m ( 0 ..^ ; 1 0 ) )
        |
        (
          sum_ i e. ( 0 ..^ ; 1 0 )
            ( 1 / ( t ` i ) )
        )
        =
        1
      }
    )
    e.
    Odd
  $.
$}
