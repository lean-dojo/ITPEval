$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_b6: the determinant of the integer matrix counting
  nonnegative solutions to a i + b j = n has the stated alternating
  ceiling-based closed form. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, 0 ..^ n is the canonical zero-based n-element index set.
  The row i, column j entry of the displayed binary map is the cardinality
  of the set of pairs (a,b) in NN0 X. NN0 satisfying
  a(i+1) + b(j+1) = n. It is therefore exactly the source matrix after
  shifting its one-based indices down by one. SetMM's maDet over ZZring is
  its integer determinant.

  The internally existential k is uniquely determined by n = 2k or
  n+1 = 2k, so k is exactly ceiling(n/2). Consequently the determinant
  equality is the annotated closed form
  (-1)^(ceiling(n/2)+1) * 2 * ceiling(n/2). Inlining the uniquely specified
  matrix and defining the ceiling through this parity characterization are
  bidirectionally equivalent to the source statement. The final declaration
  is a single unproved $a corpus statement; this database contains no $p
  proof declaration.
$)

${
  $d i j k n t $.

  putnambench-putnam-2023-b6 $a |- A. n e. NN
    E. k e. NN
      (
        (
          n = ( 2 x. k )
          \/
          ( n + 1 ) = ( 2 x. k )
        )
        /\
        (
          (
            ( ( 0 ..^ n ) maDet ZZring )
            `
            (
              i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                (
                  #
                  `
                  {
                    t e. ( NN0 X. NN0 )
                    |
                    (
                      (
                        ( ( 1st ` t ) x. ( i + 1 ) )
                        +
                        ( ( 2nd ` t ) x. ( j + 1 ) )
                      )
                      =
                      n
                    )
                  }
                )
            )
          )
          =
          (
            ( ( -u 1 ) ^ ( k + 1 ) )
            x.
            ( 2 x. k )
          )
        )
      )
  $.
$}
