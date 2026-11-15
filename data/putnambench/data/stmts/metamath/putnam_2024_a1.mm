$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2024_a1: the positive exponents for which positive integers a, b,
  and c satisfy 2 a^n + 3 b^n = 4 c^n are exactly the singleton { 1 }.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 and NN are respectively the nonnegative and positive integers.
  Thus the restricted class preserves the Lean natural-number domain for n,
  its explicit positivity condition, and the three internally existentially
  quantified positive-integer witnesses. The right-hand singleton is the
  source solution annotation {1}. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d a b c n $.

  putnambench-putnam-2024-a1 $a |-
    {
      n e. NN0
      |
      (
        0 < n
        /\
        E. a e. NN E. b e. NN E. c e. NN
          (
            (
              ( 2 x. ( a ^ n ) )
              +
              ( 3 x. ( b ^ n ) )
            )
            =
            ( 4 x. ( c ^ n ) )
          )
      )
    }
    =
    { 1 }
  $.
$}
