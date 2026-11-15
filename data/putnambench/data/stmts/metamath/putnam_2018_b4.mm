$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2018_b4: a real sequence satisfying the specified nonlinear
  recurrence is periodic if one of its terms is zero. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 is SetMM's class of all real-valued sequences indexed by the
  nonnegative integers. The recurrence is shifted to n + 3 for n in NN0,
  exactly as in the primary Lean source, avoiding truncated subtraction while
  remaining equivalent to the n >= 2 formulations in Isabelle and Rocq.

  The zero term remains internally existentially quantified. The period
  witness c ranges over NN, SetMM's positive integers, and the final universal
  equality is exactly periodicity on every nonnegative index.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d a c n x $.

  putnambench-putnam-2018-b4 $a |-
    A. a e. RR A. x e. ( RR ^m NN0 )
      (
        (
          (
            (
              ( x ` 0 ) = 1
              /\
              (
                ( x ` 1 ) = a
                /\
                ( x ` 2 ) = a
              )
            )
            /\
            A. n e. NN0
              ( x ` ( n + 3 ) )
              =
              (
                (
                  2
                  x.
                  ( x ` ( n + 2 ) )
                )
                x.
                ( x ` ( n + 1 ) )
              )
              -
              ( x ` n )
          )
          ->
          (
            E. n e. NN0
              ( x ` n ) = 0
            ->
            E. c e. NN
              A. n e. NN0
                ( x ` ( n + c ) ) = ( x ` n )
          )
        )
      )
  $.
$}
