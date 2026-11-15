$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_b1: the positive integers lying within 250 of exactly 15
  perfect squares are precisely those in the intervals 315 through 325
  and 332 through 350. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The variable n ranges over all integers, while m ranges over NN0, matching
  the integer domain for n and natural-number square indices in the Lean and
  Rocq sources. The restricted class contains exactly the natural m whose
  square has integer distance at most 250 from n; its SetMM cardinality is
  therefore the source count of nearby perfect squares.

  The right side expands the source solution set into its two inclusive
  integer intervals. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d m n $.

  putnambench-putnam-1994-b1 $a |-
    A. n e. ZZ
      (
        (
          0 < n
          /\
          (
            #
            `
            {
              m e. NN0
              |
              (
                abs
                `
                (
                  n
                  -
                  ( m ^ 2 )
                )
              )
              <_
              ( ; ; 2 5 0 )
            }
          )
          =
          ( ; 1 5 )
        )
        <->
        (
          (
            ( ; ; 3 1 5 ) <_ n
            /\
            n <_ ( ; ; 3 2 5 )
          )
          \/
          (
            ( ; ; 3 3 2 ) <_ n
            /\
            n <_ ( ; ; 3 5 0 )
          )
        )
      )
  $.
$}
