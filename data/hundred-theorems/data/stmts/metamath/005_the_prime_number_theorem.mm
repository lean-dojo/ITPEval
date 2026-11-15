$(
  Statement-only formalization of "The Prime Number Theorem" from Hundred
  Theorems item 005: the ratio of the number of primes at most n to
  n / log(n) converges to 1. This file contains no proof.
$)

$[ library/set.mm $]

$(
  Every mathematical symbol below is grounded in the imported set.mm
  database. In particular, ppi is the real prime-counting function defined by
  df-ppi, log is the natural logarithm, and RR and NN0 are the standard real
  and nonnegative-integer classes.

  The assertion is the epsilon-N expansion of the sequential limit in the
  source theorem: for every positive real error e, all natural n beyond some
  natural threshold m make the absolute difference from 1 smaller than e.
  Since df-ppi counts the primes less than or equal to its argument, ppi at a
  natural n is definitionally the source numerator. The final declaration is
  an unproved $a statement.
$)

hundred-theorems-005-prime-number-theorem $a
  |- A. e e. RR
       ( 0 < e ->
         E. m e. NN0
           A. n e. NN0
             ( m <_ n ->
               ( abs ` ( ( ( ppi ` n ) / ( n / ( log ` n ) ) ) - 1 ) )
                 < e ) ) )
$.
