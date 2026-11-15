$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_a3: the determinants of the n-by-n real matrices whose
  entries are cos(1 + n i + j) converge to zero. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  For each n in NN0, the carrier 0 ..^ n is the canonical zero-based
  n-element index set. Thus the row-i, column-j entry below is
  cos(1 + n*i + j), so reading rows from left to right gives precisely
  cos(1), cos(2), ..., cos(n^2). SetMM's maDet over RRfld is the real
  determinant, and ~~> is real-sequence convergence.

  Inlining the uniquely specified source matrix is definitionally
  equivalent to universally quantifying that matrix under its entrywise
  defining hypothesis. The determinant at n = 0 does not affect the
  limit. The target zero is the solution annotated in both ground-truth
  sources. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d i j n $.

  putnambench-putnam-2009-a3 $a |-
    (
      n e. NN0 |->
        (
          ( ( 0 ..^ n ) maDet RRfld )
          `
          (
            i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
              (
                cos
                `
                (
                  1
                  +
                  ( ( n x. i ) + j )
                )
              )
          )
        )
    )
    ~~>
    0
  $.
$}
