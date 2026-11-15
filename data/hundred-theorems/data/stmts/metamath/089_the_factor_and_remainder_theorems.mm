$(
  Statement-only formalization of "The Factor and Remainder Theorems" from
  the Hundred Theorems corpus artifact 089: for a polynomial over a
  commutative ring, division by the monic linear polynomial X - a has
  constant remainder p(a), and X - a divides p exactly when a is a root.
  This file contains no proof.
$)

$[ library/set.mm $]

$(
  Poly1 ` R is the finite-support univariate polynomial ring over R.
  var1 ` R is its indeterminate, algSc embeds coefficients as constant
  polynomials, and eval1 evaluates a polynomial at a coefficient.  The
  existential quotient identity is the remainder theorem stated without a
  division operation; its constant summand is exactly the remainder p(a).
  The second conjunct is the factor theorem and its converse.  The following
  declaration is an unproved $a assertion; this file has no $p proof
  statement.
$)

${
  $d F N Q R $.

  hundred-theorems-089-factor-and-remainder $a |- (
    A. R e. CRing
    A. N e. ( Base ` R )
    A. F e. ( Base ` ( Poly1 ` R ) )
      (
        E. Q e. ( Base ` ( Poly1 ` R ) )
          F =
            (
              (
                (
                  ( var1 ` R )
                  ( -g ` ( Poly1 ` R ) )
                  ( ( algSc ` ( Poly1 ` R ) ) ` N )
                )
                ( .r ` ( Poly1 ` R ) )
                Q
              )
              ( +g ` ( Poly1 ` R ) )
              (
                ( algSc ` ( Poly1 ` R ) )
                `
                ( ( ( eval1 ` R ) ` F ) ` N )
              )
            )
        /\
        (
          (
            (
              ( var1 ` R )
              ( -g ` ( Poly1 ` R ) )
              ( ( algSc ` ( Poly1 ` R ) ) ` N )
            )
            ( ||r ` ( Poly1 ` R ) )
            F
          )
          <->
          ( ( ( eval1 ` R ) ` F ) ` N ) = ( 0g ` R )
        )
      )
  ) $.
$}
