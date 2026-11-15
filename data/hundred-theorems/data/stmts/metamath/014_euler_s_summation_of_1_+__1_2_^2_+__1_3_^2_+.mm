$(
  Statement-only formalization of "Euler's Summation of 1 + (1/2)^2 + (1/3)^2 + ..."
  from Hundred Theorems item 014: the real reciprocal-square series converges to pi^2 / 6.
  This file contains no proof.
$)

$[ library/set.mm $]

$(
  Every mathematical symbol below is grounded in the imported set.mm
  database. RR and NN0 are the standard real and nonnegative-integer classes,
  _pi is the real number pi, and the arithmetic, order, absolute-value, and
  restricted-quantifier symbols have their standard set.mm definitions.

  The expression

    sum_ k e. ( 1 ... n ) ( 1 / ( k ^ 2 ) )

  uses set.mm's finite-sum binder: k is formally bound over the integer
  interval from 1 through n. For n in NN0 this is the n-term partial sum

    1 / 1^2 + 1 / 2^2 + ... + 1 / n^2.

  The assertion is the epsilon-N expansion of convergence of these real
  partial sums to (_pi ^ 2) / 6. The zero-based Lean form is equivalent
  because its index-zero term is zero in the real field, and successor
  reindexing gives the displayed finite sums. The final declaration is an
  unproved $a statement.
$)

${
  $d e k m n $.

  hundred-theorems-014-euler-reciprocal-squares $a
    |- A. e e. RR
         ( 0 < e ->
           E. m e. NN0
             A. n e. NN0
               ( m <_ n ->
                 ( abs ` (
                     ( sum_ k e. ( 1 ... n ) ( 1 / ( k ^ 2 ) ) )
                     - ( ( _pi ^ 2 ) / 6 )
                   ) ) < e ) )
  $.
$}
