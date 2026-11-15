$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_b1: classification of the integer vectors whose removal from
  the 3-by-101 integer grid leaves a partition into two sets of equal size
  and equal vector sum. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P18B1Grid is the set of integer ordered pairs (a,b) with 0 <= a <= 2
  and 0 <= b <= 100. Ordered pairs are definitionally equivalent to the
  source's two-coordinate integer vectors.

  The existential sets Q and R are disjoint, cover the grid with v removed,
  have equal finite cardinality, and have equal sums in both coordinates.
  The right side is exactly the source solution: v = (1,b) for an even
  integer b between 0 and 100. Substituting the source definitions of P and
  Pvdiff gives the displayed biconditional in both directions.

  Every declaration below is an unproved $a statement encoding; this
  database contains no $p proof declaration.
$)

$c P18B1Grid $.

p18b1-grid-syntax $a class P18B1Grid $.

p18b1-grid-definition $a |-
  P18B1Grid = ( ( 0 ... 2 ) X. ( 0 ... ; 1 0 0 ) ) $.

${
  $d b q r s t v $.

  putnambench-putnam-2018-b1 $a |- A. v e. ( ZZ X. ZZ )
    (
      (
        v e. P18B1Grid
        /\
        E. s e. ~P P18B1Grid
          E. t e. ~P P18B1Grid
            (
              ( s u. t ) = ( P18B1Grid \ { v } )
              /\
              (
                ( s i^i t ) = (/)
                /\
                (
                  ( # ` s ) = ( # ` t )
                  /\
                  (
                    (
                      sum_ q e. s ( 1st ` q )
                    )
                    =
                    (
                      sum_ r e. t ( 1st ` r )
                    )
                    /\
                    (
                      sum_ q e. s ( 2nd ` q )
                    )
                    =
                    (
                      sum_ r e. t ( 2nd ` r )
                    )
                  )
                )
              )
            )
      )
      <->
      E. b e. ( 0 ... ; 1 0 0 )
        (
          2 || b
          /\
          v = <. 1 , b >.
        )
    )
  $.
$}
