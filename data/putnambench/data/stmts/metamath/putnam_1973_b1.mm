$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1973_b1: an integer family of length 2n+1 is constant if every
  deletion leaves 2n entries that split into two n-entry sets of equal sum.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The index set is the inclusive natural interval 1 ... (2n+1), and a ranges
  over all integer-valued functions on that exact finite carrier. Each S is
  an arbitrary 2n-element subset of the carrier, and its balancing n-element
  subset T remains existentially quantified inside the universal quantifier
  over S. Since T is a subset of S and both have sizes n and 2n, S \ T is
  the complementary n-element part.

  Thus the antecedent is precisely the equal-sum partition condition after
  any one indexed entry is removed, including repeated integer values at
  distinct indices. The conclusion states that all indexed entries are
  equal. The final declaration is the single unproved $a corpus statement;
  this database contains no $p proof statement.
$)

${
  $d S T a i j n $.

  putnambench-putnam-1973-b1 $a |- A. n e. NN0
    A. a e. ( ZZ ^m ( 1 ... ( ( 2 x. n ) + 1 ) ) )
      (
        (
          A. S e.
            {
              S e. ~P ( 1 ... ( ( 2 x. n ) + 1 ) ) |
                ( # ` S ) = ( 2 x. n )
            }
            E. T e. { T e. ~P S | ( # ` T ) = n }
              (
                sum_ i e. T ( a ` i )
              )
              =
              (
                sum_ i e. ( S \ T ) ( a ` i )
              )
        )
        ->
        A. i e. ( 1 ... ( ( 2 x. n ) + 1 ) )
        A. j e. ( 1 ... ( ( 2 x. n ) + 1 ) )
          ( a ` i ) = ( a ` j )
      )
  $.
$}
