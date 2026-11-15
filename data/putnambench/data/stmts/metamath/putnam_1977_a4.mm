$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1977_a4: evaluation on the open unit interval of a real series
  with powers indexed by powers of two as the rational function x/(1-x).
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For each real x with 0 < x < 1, the NN0-indexed sequence consists of the
  finite partial sums through index n of

    x^(2^k) / (1 - x^(2^(k+1))).

  Convergence of these partial sums to x/(1-x) is the standard sequence-limit
  encoding of the infinite-sum equality in the Lean and Isabelle sources and
  the intended convergence statement in the Rocq source. The inclusive
  partial-sum convention differs from an exclusive upper bound by only the
  indexing of the same series.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d k n x $.

  putnambench-putnam-1977-a4 $a |- A. x e. RR
    (
      (
        0 < x
        /\
        x < 1
      )
      ->
      (
        n e. NN0 |->
          sum_ k e. ( 0 ... n )
            (
              ( x ^ ( 2 ^ k ) )
              /
              (
                1
                -
                ( x ^ ( 2 ^ ( k + 1 ) ) )
              )
            )
      )
      ~~>
      ( x / ( 1 - x ) )
    )
  $.
$}
