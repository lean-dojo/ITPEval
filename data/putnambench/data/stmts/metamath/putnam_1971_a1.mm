$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_a1: every set of nine lattice points in three-dimensional
  real space has an integer lattice point in the interior of a segment
  joining two distinct points of the set. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Integer triples are represented by the integer-valued functions
  ZZ ^m ( 1 ... 3 ). The witness u is internally existential, and its
  coordinatewise equality with t P + (1-t) Q for 0 < t < 1 is exactly
  membership in the open segment from P to Q.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d P Q S j t u $.

  putnambench-putnam-1971-a1 $a |- A. S
    (
      (
        S C_ ( ZZ ^m ( 1 ... 3 ) )
        /\
        ( # ` S ) = 9
      )
      ->
      E. P e. S E. Q e. S
        (
          P =/= Q
          /\
          E. u e. ( ZZ ^m ( 1 ... 3 ) )
          E. t e. ( 0 (,) 1 )
            u =
              (
                j e. ( 1 ... 3 ) |->
                  (
                    ( t x. ( P ` j ) )
                    +
                    ( ( 1 - t ) x. ( Q ` j ) )
                  )
              )
        )
    )
  $.
$}
