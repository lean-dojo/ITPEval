$(
  Statement-only formalization of "The Fundamental Theorem of Algebra" from
  Hundred Theorems item 002: every nonconstant univariate polynomial over the
  complex numbers has a complex root. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The included SetMM library supplies the complex numbers CC, complex
  polynomials Poly, polynomial degree deg, strict order, function application,
  equality, and first-order quantifiers with set-variable binders.

  For a complex polynomial, positive degree is equivalent to nonconstancy.
  Thus the assertion below universally quantifies the polynomial and
  existentially quantifies its complex root.
$)

hundred-theorems-002-fundamental-theorem-of-algebra $a
  |- A. f ( ( f e. ( Poly ` CC ) /\ 0 < ( deg ` f ) ) ->
       E. z e. CC ( f ` z ) = 0 )
$.
