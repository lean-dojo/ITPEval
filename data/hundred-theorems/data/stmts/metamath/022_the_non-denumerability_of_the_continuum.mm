$(
  Statement-only formalization of Hundred Theorems item 022, the
  non-denumerability of the continuum.

  The assertion is exactly the proposition proved by set.mm theorem ruc:
  there is no injection from the real numbers into the natural numbers.
$)

$[ library/set.mm $]

hundred-theorems-022-real-uncountability $a
  |- NN ~< RR
$.
