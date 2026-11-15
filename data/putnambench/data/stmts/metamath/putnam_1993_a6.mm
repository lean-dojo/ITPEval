$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1993_a6: a self-indexing sequence of 2s and 3s has its positions
  occupied by 2 characterized by a real Beatty-type floor sequence. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  A ranges over integer-valued sequences indexed by NN0. The first antecedent
  forces every value to be 2 or 3, so this is equivalent to the natural-valued
  sequence type in the Isabelle source. The set 0 ..^ N consists exactly of
  the N indices 0 through N - 1, matching both source prefix sums.

  The witness m ranges over NN0, preserving the nonnegative witness specified
  by Isabelle and by the problem statement. This is also equivalent to Lean's
  integer witness: the antecedent gives A(0) = 2 and then A(3) = 2, so any
  parameter satisfying the conclusion is nonzero; replacing it by its
  absolute value and replacing an integer witness by its absolute value
  preserves every nonnegative floor value. Conversely, for a positive
  parameter, a negative integer witness cannot produce a nonnegative floor
  value, while NN0 is contained in ZZ.

  Set.mm's |_ is the floor function on the reals. The final declaration is
  the single unproved $a corpus statement; this database contains no $p proof
  statement.
$)

${
  $d A N i m n r $.

  putnambench-putnam-1993-a6 $a |- A. A e. ( ZZ ^m NN0 )
    (
      (
        A. n e. NN0
          (
            ( A ` n ) = 2
            \/
            ( A ` n ) = 3
          )
        /\
        A. n e. NN0
          (
            ( A ` n ) = 2
            <->
            E. N e. NN0
              n
              =
              (
                sum_ i e. ( 0 ..^ N )
                  ( ( A ` i ) + 1 )
              )
          )
      )
      ->
      E. r e. RR
        A. n e. NN0
          (
            ( A ` n ) = 2
            <->
            E. m e. NN0
              ( n + 1 )
              =
              ( 1 + ( |_ ` ( r x. m ) ) )
          )
    )
  $.
$}
