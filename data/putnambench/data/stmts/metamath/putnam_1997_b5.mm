$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1997_b5: consecutive heights of base-two tetration are congruent
  modulo every natural height n at least two. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  t ranges over all functions from NN0 X. NN0 to NN0. The two antecedent
  conjuncts are exactly the source equations t(a,0) = 1 and
  t(a,m+1) = a^t(a,m), for every natural base a and height m.

  For natural values, equality of the two remainders modulo n is equivalent
  to the source natural-number congruence. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d a m n t $.

  putnambench-putnam-1997-b5 $a |-
    A. t e. ( NN0 ^m ( NN0 X. NN0 ) )
    A. n e. NN0
      (
        (
          2 <_ n
          /\
          (
            A. a e. NN0
              ( t ` <. a , 0 >. ) = 1
            /\
            A. a e. NN0 A. m e. NN0
              ( t ` <. a , ( m + 1 ) >. )
              =
              ( a ^ ( t ` <. a , m >. ) )
          )
        )
        ->
        (
          ( ( t ` <. 2 , n >. ) mod n )
          =
          ( ( t ` <. 2 , ( n - 1 ) >. ) mod n )
        )
      )
  $.
$}
