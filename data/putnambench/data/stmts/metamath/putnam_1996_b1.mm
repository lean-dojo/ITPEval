$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1996_b1: the number of minimal selfish subsets of the positive
  integer interval from one through n equals the specified natural-valued
  solution function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN, 1 ... n is the source interval {1, ..., n}, ~P is its full
  power set, # is finite cardinality, and C. is proper subsethood. Thus the
  restricted class abstraction contains exactly the selfish subsets s for
  which no proper subset ss is selfish.

  Fibci is SetMM's canonical Fibonacci sequence, beginning with 0 and 1.
  The predicate selfish is inlined using its source definition. Every
  declaration below is an unproved $a statement, and this database contains
  no $p proof statement.
$)

${
  $d n s t $.

  putnambench-putnam-1996-b1 $a |- A. n e. NN
    (
      #
      `
      {
        s e. ~P ( 1 ... n ) |
        (
          ( # ` s ) e. s
          /\
          A. t e. ~P s
            (
              t C. s
              ->
              -. ( ( # ` t ) e. t )
            )
        )
      }
    )
    =
    ( Fibci ` n )
  $.
$}
