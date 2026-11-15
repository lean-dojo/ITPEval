$(
  Statement-only formalization of "Pythagorean Theorem" from Hundred
  Theorems item 004: orthogonal vectors in an arbitrary real inner-product
  space satisfy the squared-norm identity. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The imported set.mm definitions give semantic content to every operation
  in the assertion. CPreHil is the class of subcomplex pre-Hilbert spaces;
  requiring the Scalar component to equal RRfld selects real scalar spaces.
  Base, .i, +g, and norm are the structure's carrier, inner product, vector
  addition, and norm projections. The set.mm theorem nmsq identifies the
  displayed squared norms with self inner products.

  Metamath assertion variables are schematic, so W, A, and B are universally
  quantified subject to the displayed structure and carrier conditions. The
  final declaration is an unproved $a statement, not a proof.
$)

hundred-pythagorean-theorem $a |- (
  (
    W e. CPreHil
    /\
    (
      ( Scalar ` W ) = RRfld
      /\
      (
        A e. ( Base ` W )
        /\
        (
          B e. ( Base ` W )
          /\
          ( A ( .i ` W ) B ) = 0
        )
      )
    )
  )
  ->
  (
    ( ( ( norm ` W ) ` ( A ( +g ` W ) B ) ) ^ 2 )
    =
    (
      ( ( ( norm ` W ) ` A ) ^ 2 )
      +
      ( ( ( norm ` W ) ` B ) ^ 2 )
    )
  )
) $.
