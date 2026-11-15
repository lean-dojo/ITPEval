$(
  Statement-only formalization of "Leibniz's Series for Pi" from Hundred
  Theorems item 026: the real partial sums of the alternating odd-reciprocal
  series converge to pi / 4. This file contains no proof.
$)

$[ library/set.mm $]

$(
  Every mathematical symbol below is grounded in the imported set.mm
  database. RR and NN0 are the standard real and nonnegative-integer classes,
  _pi is the real number pi, and the arithmetic, order, absolute-value,
  finite-sum, and restricted-quantifier symbols have their standard set.mm
  definitions.

  For n in NN0, the expression

    sum_ k e. ( 0 ..^ n )
      ( ( ( -u 1 ) ^ k ) / ( ( 2 x. k ) + 1 ) )

  is the n-term real partial sum

    1 - 1/3 + 1/5 - ... + (-1)^(n-1)/(2n-1).

  The assertion is the epsilon-N expansion of convergence of these partial
  sums to _pi / 4. The half-open interval 0 ..^ n is the set.mm rendering of
  the zero-based range used by the Lean source and gives the same series as
  the HOL Light and Rocq sources. The final declaration is an unproved $a
  statement.
$)

hundred-theorems-026-leibniz-series-for-pi $a
  |- A. e e. RR
       ( 0 < e ->
         E. m e. NN0
           A. n e. NN0
             ( m <_ n ->
               ( abs ` (
                   ( sum_ k e. ( 0 ..^ n )
                       ( ( ( -u 1 ) ^ k ) / ( ( 2 x. k ) + 1 ) ) )
                   - ( _pi / 4 )
                 ) ) < e ) ) )
$.
