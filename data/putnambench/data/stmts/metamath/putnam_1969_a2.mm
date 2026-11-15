$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1969_a2: the determinant of the n-by-n real matrix whose
  (i,j)-entry is the absolute difference of its indices. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The index set 0 ..^ n is {0,...,n-1}. The binary map is therefore exactly
  the real matrix with entry abs(i-j), and maDet is SetMM's determinant over
  the real field.

  The assertion uses every positive natural n, as in the Isabelle source.
  At n = 1 both sides are zero; for n >= 2 its natural exponents agree with
  the integer exponents in the Lean source. The final declaration is the
  single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d i j n $.

  putnambench-putnam-1969-a2 $a |- A. n e. NN
    (
      (
        ( ( 0 ..^ n ) maDet RRfld )
        `
        (
          i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
            ( abs ` ( i - j ) )
        )
      )
      =
      (
        ( ( -u 1 ) ^ ( n - 1 ) )
        x.
        (
          ( n - 1 )
          x.
          ( 2 ^ ( n - 2 ) )
        )
      )
    )
  $.
$}
