$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2021_b5: positive powers of a very odd integer square matrix remain
  very odd, where every nonempty principal minor has odd determinant. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, 0 ..^ n is the canonical n-element carrier and
  Base ` ((0 ..^ n) Mat ZZring) is the full set of integer n-by-n matrices.
  P21B5VeryOdd A n quantifies over every nonempty subset S of that carrier,
  restricts both matrix indices to S, and requires the resulting principal
  determinant to be odd.

  Simultaneously reindexing the rows and columns of a principal submatrix
  leaves its determinant unchanged, so the subset formulation is equivalent
  to the injective-reindexing formulation in the Lean source. The mulGrp
  exponent is ordinary matrix-ring exponentiation. Every declaration below
  is an unproved $a statement encoding; this database contains no $p proof
  declaration.
$)

$c P21B5VeryOdd $.

p21b5-very-odd-syntax $a wff ( P21B5VeryOdd A n ) $.

${
  $d A S i j n $.

  p21b5-very-odd-definition $a |- (
    ( P21B5VeryOdd A n )
    <->
    A. S e. ( ~P ( 0 ..^ n ) \ { (/) } )
      (
        (
          (
            S maDet ZZring
          )
          `
          (
            i e. S , j e. S |->
              ( A ` <. i , j >. )
          )
        )
        mod
        2
      )
      =
      1
  ) $.
$}

${
  $d A k n $.

  putnambench-putnam-2021-b5 $a |-
    A. n e. NN
      A. A e. ( Base ` ( ( 0 ..^ n ) Mat ZZring ) )
        (
          ( P21B5VeryOdd A n )
          ->
          A. k e. NN
            (
              P21B5VeryOdd
              (
                k
                ( .g ` ( mulGrp ` ( ( 0 ..^ n ) Mat ZZring ) ) )
                A
              )
              n
            )
        )
  $.
$}
