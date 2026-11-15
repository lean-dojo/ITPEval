$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_b6: the number of permutations with displacement at most k is
  odd exactly when n is congruent to zero or one modulo 2k+1. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  For positive n and k, the ordinal interval 0 ..^ n is the n-element
  carrier corresponding to Fin n, and Base ` ( SymGrp ` ( 0 ..^ n ) ) is
  its full set of permutations. The restricted class retains exactly those
  permutations f for which the integer absolute displacement |f(i)-i| is at
  most k at every index.

  SetMM's # operator gives the finite cardinality of this class, Odd is the
  class of odd integers, and mod expresses the two source congruences modulo
  2k+1. The zero-based carrier is equivalent to the informal one-based
  carrier by shifting every index and value by one, which preserves all
  displacements. The final declaration is the single unproved $a corpus
  statement; this database contains no proof declaration.
$)

${
  $d f i k n $.

  putnambench-putnam-2008-b6 $a |- A. n e. NN
    A. k e. NN
      (
        (
          #
          `
          {
            f e. ( Base ` ( SymGrp ` ( 0 ..^ n ) ) )
            |
            A. i e. ( 0 ..^ n )
              ( abs ` ( ( f ` i ) - i ) ) <_ k
          }
        )
        e.
        Odd
        <->
        (
          (
            n mod ( ( 2 x. k ) + 1 )
          )
          =
          0
          \/
          (
            n mod ( ( 2 x. k ) + 1 )
          )
          =
          1
        )
      )
  $.
$}
