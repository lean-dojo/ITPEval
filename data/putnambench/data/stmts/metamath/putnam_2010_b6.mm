$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2010_b6: equality of ordinary and entrywise powers of a real square
  matrix through exponent n+1 implies equality for every positive exponent.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, the carrier 0 ..^ n is the canonical n-element index set,
  and Base ` ((0 ..^ n) Mat RRfld) is the full set of real n-by-n matrices.
  The operation .g of the matrix ring's multiplicative group gives ordinary
  matrix powers, while the maps-to expression raises each real entry of A to
  the same natural exponent.

  The source function Apow is uniquely fixed at every positive exponent by
  its defining hypothesis. Substituting that entrywise definition in both
  the antecedent and conclusion is therefore bidirectionally equivalent to
  the source statement. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d a i j k n $.

  putnambench-putnam-2010-b6 $a |-
    A. n e. NN
      A. a e. ( Base ` ( ( 0 ..^ n ) Mat RRfld ) )
        (
          A. k e. ( 1 ... ( n + 1 ) )
            (
              k
              ( .g ` ( mulGrp ` ( ( 0 ..^ n ) Mat RRfld ) ) )
              a
            )
            =
            (
              i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                ( ( a ` <. i , j >. ) ^ k )
            )
          ->
          A. k e. NN
            (
              k
              ( .g ` ( mulGrp ` ( ( 0 ..^ n ) Mat RRfld ) ) )
              a
            )
            =
            (
              i e. ( 0 ..^ n ) , j e. ( 0 ..^ n ) |->
                ( ( a ` <. i , j >. ) ^ k )
            )
        )
  $.
$}
