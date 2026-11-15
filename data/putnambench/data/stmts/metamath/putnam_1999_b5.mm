$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_b5: evaluation of the determinant of an n-by-n real
  cosine matrix plus the identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The carrier 0 ..^ n has exactly n elements. Its zero-based indices i,j
  are shifted to i+1,j+1, so the displayed binary map is the source matrix
  I+A with theta definitionally replaced by 2*pi/n. SetMM's maDet over
  RRfld is the determinant of this real matrix.

  Inlining theta and the uniquely specified matrix eliminates only
  definitional parameters. The right side is the solution 1-n^2/4
  annotated in both ground-truth sources. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d i j n $.

  putnambench-putnam-1999-b5 $a |- A. n e. NN0
    (
      3 <_ n
      ->
      (
        (
          ( ( 0 ..^ n ) maDet RRfld )
          `
          (
            i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
              (
                if ( i = j , 1 , 0 )
                +
                (
                  cos
                  `
                  (
                    (
                      ( i + 1 )
                      x.
                      ( ( 2 x. _pi ) / n )
                    )
                    +
                    (
                      ( j + 1 )
                      x.
                      ( ( 2 x. _pi ) / n )
                    )
                  )
                )
              )
          )
        )
        =
        (
          1
          -
          ( ( n ^ 2 ) / 4 )
        )
      )
    )
  $.
$}
