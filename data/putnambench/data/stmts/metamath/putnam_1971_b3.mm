$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1971_b3: for every positive real starting-time offset, the set of
  later real times at which one integer lap count is twice the other has
  Lebesgue measure one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The parameter T and time t range over all reals. The condition t >= T
  makes both floor arguments nonnegative, matching the natural-valued floor
  in the Lean source, while set.mm's integer-valued floor directly matches
  the Isabelle source. The function vol is set.mm's Lebesgue measure on
  measurable subsets of the real line.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d T t $.

  putnambench-putnam-1971-b3 $a |- A. T e. RR
    (
      0 < T
      ->
      (
        vol
        `
        {
          t e. RR |
          (
            T <_ t
            /\
            ( |_ ` t )
            =
            ( 2 x. ( |_ ` ( t - T ) ) )
          )
        }
      )
      =
      1
    )
  $.
$}
