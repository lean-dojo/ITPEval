$(
  Statement-only formalization of "The Hermite-Lindemann Transcendence
  Theorem" from Hundred Theorems item 056: the complex exponential of every
  nonzero algebraic complex number is transcendental. This file contains no
  proof.
$)

$[ library/set.mm $]

$(
  The imported SetMM library defines CC as the complex numbers, exp as the
  complex exponential function, and AA as the complex algebraic numbers,
  equivalently the roots of nonzero integer polynomials. Thus the assertion
  preserves the source domain and states directly that if x is nonzero and
  algebraic, then exp(x) is not algebraic. The final declaration is an
  unproved $a statement.
$)

hundred-theorems-056-hermite-lindemann $a
  |- A. x e. CC
       ( ( x e. AA /\ x =/= 0 ) -> ( exp ` x ) e/ AA )
$.
