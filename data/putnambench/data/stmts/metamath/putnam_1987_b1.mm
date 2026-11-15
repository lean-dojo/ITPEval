$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1987_b1: evaluation of the real integral from 2 to 4 of a quotient
  involving square roots of logarithms as 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Set.mm's S. binder is the real Lebesgue integral. The closed interval
  ( 2 [,] 4 ) matches the source interval, and the integrand uses the same
  real logarithm and nonnegative square root operations. The value 1 is the
  explicit Rocq solution and is also recorded by the Lean and Isabelle
  solution annotations.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

putnambench-putnam-1987-b1 $a |- (
  S. ( 2 [,] 4 )
    (
      ( sqrt ` ( log ` ( 9 - x ) ) )
      /
      (
        ( sqrt ` ( log ` ( 9 - x ) ) )
        +
        ( sqrt ` ( log ` ( x + 3 ) ) )
      )
    )
    _d x
  =
  1
) $.
