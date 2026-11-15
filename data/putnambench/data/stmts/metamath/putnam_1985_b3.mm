$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_b3: a doubly indexed positive-integer array in which every
  positive integer occurs exactly eight times at positive indices has an
  entry a(m,n) greater than m times n for some positive m and n. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over all functions from NN0 X. NN0 to NN, which is equivalent to
  the source natural-valued array together with its everywhere-positivity
  assumption. Restricting k, m, and n to NN is equivalent to the source
  guards that those naturals are positive. SetMM's # operator equals 8
  exactly when the displayed occurrence set has eight elements, so the
  infinite index domain is not bounded or replaced by a finite table.

  The ordered-pair variable t represents the two positive indices, with 1st
  and 2nd recovering m and n. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d A k t $.

  putnambench-putnam-1985-b3 $a |-
    A. A e. ( NN ^m ( NN0 X. NN0 ) )
      (
        A. k e. NN
          (
            (
              #
              `
              {
                t e. ( NN X. NN ) |
                ( A ` t ) = k
              }
            )
            =
            8
          )
        ->
        E. t e. ( NN X. NN )
          (
            (
              ( 1st ` t )
              x.
              ( 2nd ` t )
            )
            <
            ( A ` t )
          )
      )
  $.
$}
