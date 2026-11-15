$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1983_b4: every positive natural-number sequence satisfying
  a(n+1) = a(n) + floor(sqrt(a(n))) contains a perfect square.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 is SetMM's class of nonnegative integers, so A ranges over all total
  natural-number sequences with the same indexing and value domain as the
  Isabelle source. The positive initial value and recurrence make this
  equivalent to the integer-valued formulations in Lean and Rocq. SetMM's
  sqrt is the principal square root and |_ is the real floor function.

  The square witness is restricted to NN0 without loss: an integer whose
  square is a natural sequence value can be replaced by its absolute value.
  Both the index and square root remain internally existentially quantified.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A i n s $.

  putnambench-putnam-1983-b4 $a |-
    A. A e. ( NN0 ^m NN0 )
      (
        (
          0 < ( A ` 0 )
          /\
          A. n e. NN0
            ( A ` ( n + 1 ) )
            =
            (
              ( A ` n )
              +
              ( |_ ` ( sqrt ` ( A ` n ) ) )
            )
        )
        ->
        E. i e. NN0 E. s e. NN0
          ( A ` i ) = ( s ^ 2 )
      )
  $.
$}
