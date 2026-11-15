$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1991_b1: positive initial values whose floor-square-remainder
  recurrence is eventually constant are exactly the perfect squares. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and NN are SetMM's classes of nonnegative and positive integers.
  For n in NN0, floor(sqrt(n)) is the greatest nonnegative integer m with
  m^2 <= n. Thus the displayed increment is exactly the source function
  S(n) = n - m^2, with the helper functions m and S eliminated by their
  definitions.

  The sequence is quantified over NN0-valued maps. This is equivalent to the
  Lean integer-valued presentation because a positive initial value and the
  stated recurrence keep every term nonnegative; it directly matches the
  Isabelle and Rocq domains. In the perfect-square condition the witness is
  positive, equivalent to the Rocq nonnegative witness because A is positive.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d A K a c k x $.

  putnambench-putnam-1991-b1 $a |-
    A. A e. NN A. a e. ( NN0 ^m NN0 )
      (
        (
          ( a ` 0 ) = A
          /\
          A. k e. NN0
            ( a ` ( k + 1 ) )
            =
            (
              ( a ` k )
              +
              (
                ( a ` k )
                -
                (
                  ( |_ ` ( sqrt ` ( a ` k ) ) )
                  ^
                  2
                )
              )
            )
        )
        ->
        (
          (
            E. K e. NN0 E. c e. NN0
              A. k e. NN0
                (
                  K <_ k
                  ->
                  ( a ` k ) = c
                )
          )
          <->
          E. x e. NN A = ( x ^ 2 )
        )
      )
  $.
$}
