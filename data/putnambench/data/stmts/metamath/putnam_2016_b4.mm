$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_b4: the expected determinant of A minus its transpose for a
  uniformly random binary matrix of even order. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n, 0 ..^ (2*n) is the canonical 2n-element carrier.
  The maps from its Cartesian square into {0,1} are exactly the binary
  2n by 2n matrices. Giving every such map equal weight is equivalent to
  choosing all entries independently, each uniformly from {0,1}.

  SetMM's tpos is matrix transpose, -g in the real matrix ring is matrix
  subtraction, and maDet over RRfld is the real determinant. Thus the
  quotient on the left is the source expectation. The right side inlines
  the solution (2n)! / (4^n n!). Inlining both source definitions is a
  bidirectionally equivalent definitional substitution. The final declaration
  is the single unproved $a corpus statement; there is no $p declaration.
$)

${
  $d A n $.

  putnambench-putnam-2016-b4 $a |- A. n e. NN
    (
      (
        sum_ A e.
          (
            { 0 , 1 }
            ^m
            (
              ( 0 ..^ ( 2 x. n ) )
              X.
              ( 0 ..^ ( 2 x. n ) )
            )
          )
          (
            ( ( 0 ..^ ( 2 x. n ) ) maDet RRfld )
            `
            (
              A
              ( -g ` ( ( 0 ..^ ( 2 x. n ) ) Mat RRfld ) )
              tpos A
            )
          )
      )
      /
      (
        #
        `
        (
          { 0 , 1 }
          ^m
          (
            ( 0 ..^ ( 2 x. n ) )
            X.
            ( 0 ..^ ( 2 x. n ) )
          )
        )
      )
      =
      (
        ( ! ` ( 2 x. n ) )
        /
        (
          ( 4 ^ n )
          x.
          ( ! ` n )
        )
      )
    )
  $.
$}
