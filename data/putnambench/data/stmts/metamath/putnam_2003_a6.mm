$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2003_a6: a partition of the nonnegative integers into two sets
  having equal ordered distinct-pair representation counts for every sum.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is the full set of nonnegative integers. The existential quantifiers
  range over arbitrary subsets A and B of NN0, and the union and intersection
  conditions say exactly that they form a partition.

  For each n, the restricted class over A X. A (respectively B X. B) contains
  exactly the ordered pairs of distinct elements whose sum is n. Such a class
  is finite because both coordinates lie between 0 and n, so set.mm's
  cardinality agrees with the natural-valued representation count in the
  sources. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof declaration.
$)

${
  $d A B n t $.

  putnambench-putnam-2003-a6 $a |- E. A e. ~P NN0
    E. B e. ~P NN0
      (
        (
          ( A u. B ) = NN0
          /\
          ( A i^i B ) = (/)
        )
        /\
        A. n e. NN0
          (
            #
            `
            {
              t e. ( A X. A )
              |
              (
                ( 1st ` t ) =/= ( 2nd ` t )
                /\
                ( ( 1st ` t ) + ( 2nd ` t ) ) = n
              )
            }
          )
          =
          (
            #
            `
            {
              t e. ( B X. B )
              |
              (
                ( 1st ` t ) =/= ( 2nd ` t )
                /\
                ( ( 1st ` t ) + ( 2nd ` t ) ) = n
              )
            }
          )
      )
  $.
$}
