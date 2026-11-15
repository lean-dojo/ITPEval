$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_a6: for 2n strictly increasing real points between -1 and 1,
  the greatest number of prescribed odd-power interval-sum identities is n.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  A sequence x is represented as a function from 1 ... (2 x. n) to RR.
  This is equivalent to the source's total natural-indexed representation:
  every finite strictly increasing real sequence can be extended strictly
  monotonically before and after the indices used here.

  The first existential clause says that the required identities hold for
  every k from 1 through n. The universal clause says that any nonnegative m
  admitting such a sequence is at most n. Together these clauses state that
  n is the greatest admissible m, with the witness remaining internally
  existentially quantified. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d i k m n x $.

  putnambench-putnam-2022-a6 $a |- A. n e. NN
    (
      E. x e. ( RR ^m ( 1 ... ( 2 x. n ) ) )
        (
          (
            (
              -u 1 < ( x ` 1 )
              /\
              A. i e. ( 1 ... ( ( 2 x. n ) - 1 ) )
                ( x ` i ) < ( x ` ( i + 1 ) )
            )
            /\
            ( x ` ( 2 x. n ) ) < 1
          )
          /\
          A. k e. ( 1 ... n )
            (
              sum_ i e. ( 1 ... n )
                (
                  (
                    ( x ` ( 2 x. i ) )
                    ^
                    ( ( 2 x. k ) - 1 )
                  )
                  -
                  (
                    ( x ` ( ( 2 x. i ) - 1 ) )
                    ^
                    ( ( 2 x. k ) - 1 )
                  )
                )
            )
            =
            1
        )
      /\
      A. m e. NN0
        (
          E. x e. ( RR ^m ( 1 ... ( 2 x. n ) ) )
            (
              (
                (
                  -u 1 < ( x ` 1 )
                  /\
                  A. i e. ( 1 ... ( ( 2 x. n ) - 1 ) )
                    ( x ` i ) < ( x ` ( i + 1 ) )
                )
                /\
                ( x ` ( 2 x. n ) ) < 1
              )
              /\
              A. k e. ( 1 ... m )
                (
                  sum_ i e. ( 1 ... n )
                    (
                      (
                        ( x ` ( 2 x. i ) )
                        ^
                        ( ( 2 x. k ) - 1 )
                      )
                      -
                      (
                        ( x ` ( ( 2 x. i ) - 1 ) )
                        ^
                        ( ( 2 x. k ) - 1 )
                      )
                    )
                )
                =
                1
            )
          ->
          m <_ n
        )
    )
  $.
$}
