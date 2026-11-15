$(
  Statement-only formalization of Hundred Theorems item 042, the sum of the
  reciprocals of the positive triangular numbers.

  Since the k-th positive triangular number is k(k+1)/2, the displayed
  summand is its reciprocal. This is the proposition proved by set.mm theorem
  trirecip.
$)

$[ library/set.mm $]

hundred-theorems-042-triangular-reciprocals $a
  |- sum_ k e. NN ( 2 / ( k x. ( k + 1 ) ) ) = 2
$.
