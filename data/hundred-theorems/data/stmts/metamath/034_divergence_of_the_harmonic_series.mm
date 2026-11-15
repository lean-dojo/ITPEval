$(
  Statement-only formalization of "Divergence of the Harmonic Series" from Hundred Theorems
  item 034: the real harmonic partial sums tend to positive infinity. This file contains no
  proof.
$)

$[ library/set.mm $]

$(
  Every mathematical symbol below is grounded in the imported set.mm database.
  RR and NN0 are the standard real and nonnegative-integer classes; <_ is
  non-strict order, / is real division on these arguments, and sum_ is
  set.mm's finite-sum binder.

  For n in NN0,

    sum_ k e. ( 1 ... n ) ( 1 / k )

  is the sum from k = 1 through n. It is identical, by successor reindexing,
  to the n-term partial sum over i = 0, ..., n - 1 of 1 / (i + 1) used by the
  Lean and Agda sources. The assertion says that for every real bound b there
  is a natural threshold m after which every harmonic partial sum is at least
  b. This is the restricted-quantifier expansion of convergence to positive
  infinity and is equivalent here to divergence of the harmonic series.

  The final declaration is an unproved $a statement.
$)

hundred-theorems-034-harmonic-series-diverges $a
  |- A. b e. RR
       E. m e. NN0
         A. n e. NN0
           ( m <_ n ->
             b <_ ( sum_ k e. ( 1 ... n ) ( 1 / k ) ) )
$.
