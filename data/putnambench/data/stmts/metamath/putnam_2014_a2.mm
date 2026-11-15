$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_a2: the determinant of the n-by-n real matrix whose
  (i,j)-entry is the reciprocal of min(i,j), with one-based indices.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, 0 ..^ n is the canonical zero-based carrier for Fin n.
  Hence the entry below is 1/min(i+1,j+1): the conditional selects i+1
  exactly when i <= j, and otherwise selects j+1. SetMM's maDet over RRfld
  is the real determinant.

  Inlining this uniquely specified matrix is definitionally equivalent to
  universally quantifying a matrix under the source's entrywise defining
  hypothesis. The right side is the solution annotated in both ground-truth
  sources, (-1)^(n-1) / ((n-1)! n!). The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d i j n $.

  putnambench-putnam-2014-a2 $a |- A. n e. NN
    (
      (
        ( ( 0 ..^ n ) maDet RRfld )
        `
        (
          i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
            (
              1
              /
              if (
                i <_ j ,
                ( i + 1 ) ,
                ( j + 1 )
              )
            )
        )
      )
      =
      (
        ( ( -u 1 ) ^ ( n - 1 ) )
        /
        (
          ( ! ` ( n - 1 ) )
          x.
          ( ! ` n )
        )
      )
    )
  $.
$}
