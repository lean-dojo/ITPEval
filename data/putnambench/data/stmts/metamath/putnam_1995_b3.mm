$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_b3: the sum of determinants obtained by arranging every
  n-squared-digit positive decimal integer row by row in an n by n matrix.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, 0 ..^ (n^2) is the set of digit positions and
  0 ..^ n is the row and column index set. The restricted function class
  contains every decimal digit function on those positions whose leading
  digit is nonzero. Restriction to 0 ..^ (n^2) and extension by zero give a
  bijection with the source functions on NN0 that vanish at and beyond n^2.

  The binary map sends row i and column j to digit i*n+j, so maDet over
  ZZring is exactly the source integer determinant. The finite sum ranges
  over all n-squared-digit positive decimal integers. The right side inlines
  the annotated solution: 45 for n = 1, 10 times 45 squared for n = 2, and
  zero otherwise. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d f i j n $.

  putnambench-putnam-1995-b3 $a |- A. n e. NN
    (
      sum_ f e.
        {
          f e.
            (
              ( 0 ... 9 )
              ^m
              ( 0 ..^ ( n ^ 2 ) )
            )
          |
          ( f ` 0 ) =/= 0
        }
        (
          ( ( 0 ..^ n ) maDet ZZring )
          `
          (
            i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
              ( f ` ( ( i x. n ) + j ) )
          )
        )
      =
      if
      (
        n = 1 ,
        ; 4 5 ,
        if
        (
          n = 2 ,
          ( ; 1 0 x. ( ; 4 5 ^ 2 ) ) ,
          0
        )
      )
    )
  $.
$}
