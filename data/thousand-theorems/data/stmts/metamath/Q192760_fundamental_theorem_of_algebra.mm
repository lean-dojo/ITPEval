$(
  Statement-only formalization of Thousand Theorems corpus artifact Q192760
  (thousand-theorems__metamath__Q192760), "Fundamental theorem of algebra":
  the complex numbers are algebraically closed, equivalently every
  nonconstant univariate complex polynomial has a complex root. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's Poly ` CC is the class of complex polynomial functions, deg is
  polynomial degree, and function application evaluates a polynomial.
  Positive degree is equivalent to nonconstancy for a complex polynomial.
  Therefore the assertion is the standard polynomial-root characterization
  of the Lean instance Complex.isAlgClosed.

  The final $a declaration is the single unproved corpus statement. This
  candidate contributes no $p proof statement.
$)

thousand-theorems-q192760-fundamental-theorem-of-algebra $a
  |- A. f ( ( f e. ( Poly ` CC ) /\ 0 < ( deg ` f ) ) ->
       E. z e. CC ( f ` z ) = 0 )
$.
