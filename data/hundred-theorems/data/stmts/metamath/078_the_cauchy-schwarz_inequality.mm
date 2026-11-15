$(
  Statement-only formalization of "The Cauchy-Schwarz Inequality" from the
  Hundred Theorems corpus artifact 078: in every real inner-product space,
  the absolute value of the inner product of two vectors is at most the
  product of their norms. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The hypotheses require an arbitrary pre-Hilbert space whose scalar field is
  the real field, together with two arbitrary vectors in its base set. The
  conclusion is the standard absolute-value form of the Cauchy-Schwarz
  inequality. This is an unproved statement assertion, not a proof.
$)

hundred-theorems-078-cauchy-schwarz $a |- (
  (
    W e. CPreHil
    /\
    (
      ( Scalar ` W ) = RRfld
      /\
      (
        A e. ( Base ` W )
        /\
        B e. ( Base ` W )
      )
    )
  )
  ->
  (
    ( abs ` ( A ( .i ` W ) B ) )
    <_
    (
      ( ( norm ` W ) ` A )
      x.
      ( ( norm ` W ) ` B )
    )
  )
) $.
