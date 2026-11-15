$(
  Statement-only formalization of Thousand Theorems corpus artifact Q810431
  (thousand-theorems__metamath__Q810431), "Basel problem": the real series of
  reciprocal squares of the natural numbers sums to pi squared divided by
  six. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR and NN0 are set.mm's standard real numbers and nonnegative integers, and
  _pi is the real number pi. The finite-sum binder

    sum_ k e. ( 1 ... n ) ( 1 / ( k ^ 2 ) )

  is the partial sum from one through n. The assertion below is the
  epsilon-N characterization of convergence of these real partial sums to
  (_pi ^ 2) / 6. This is equivalent to the source's NN0-indexed HasSum
  statement because division by zero is zero in the real field, so its
  index-zero term is zero.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

thousand-theorems-metamath-q810431-basel-problem $a
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
