$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_a2: the determinant of the intersection-incidence matrix of
  all nonempty subsets of {1,...,n}. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, 0 ..^ (2^n-1) is an index carrier corresponding to
  Fin (2^n-1), and 1 ... n is the source set {1,...,n}. The map S ranges
  over arbitrary subsets of the natural numbers before the range hypothesis
  requires its values to enumerate exactly the nonempty subsets of 1 ... n.

  Base ` ((0 ..^ (2^n-1)) Mat RRfld) is the full real square-matrix space
  on that carrier. The entry hypothesis is exactly zero for disjoint indexed
  subsets and one otherwise, while maDet is the real determinant. The
  source solution is inlined as 1 when n = 1 and -1 otherwise.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d M S i j n $.

  putnambench-putnam-2018-a2 $a |- A. n e. NN
    A. S e.
      (
        ( ~P NN0 )
        ^m
        ( 0 ..^ ( ( 2 ^ n ) - 1 ) )
      )
      A. M e.
        (
          Base
          `
          (
            ( 0 ..^ ( ( 2 ^ n ) - 1 ) )
            Mat
            RRfld
          )
        )
        (
          ran S
          =
          (
            ~P ( 1 ... n )
            \
            { (/) }
          )
          ->
          (
            A. i e. ( 0 ..^ ( ( 2 ^ n ) - 1 ) )
              A. j e. ( 0 ..^ ( ( 2 ^ n ) - 1 ) )
                ( M ` <. i , j >. )
                =
                if
                (
                  ( ( S ` i ) i^i ( S ` j ) ) = (/) ,
                  0 ,
                  1
                )
            ->
            (
              (
                ( ( 0 ..^ ( ( 2 ^ n ) - 1 ) ) maDet RRfld )
                `
                M
              )
              =
              if
              (
                n = 1 ,
                1 ,
                ( -u 1 )
              )
            )
          )
        )
  $.
$}
