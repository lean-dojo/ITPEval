$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1984_b2: the minimum of
  (u - v)^2 + (sqrt(2 - u^2) - 9/v)^2 over real numbers satisfying
  0 < u < sqrt(2) and v > 0 is 8. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The objective is inlined pointwise, matching the defining equation for f
  in all ground-truth sources. The first conjunct states that 8 is a lower
  bound on the full real domain specified by the problem. The second conjunct
  keeps the attaining values of u and v existentially quantified inside the
  statement and asserts that the same objective equals 8 there. Together
  these clauses are exactly the explicit IsLeast characterization of the
  minimum.

  Set.mm's sqrt is the principal square root; under 0 < u < sqrt(2), its
  argument 2 - u^2 is a nonnegative real, so it agrees with the real square
  root in the sources. The final declaration is the single unproved $a corpus
  statement; this database contains no $p proof statement.
$)

${
  $d u v $.

  putnambench-putnam-1984-b2 $a |- (
    A. u e. RR A. v e. RR
      (
        (
          (
            0 < u
            /\
            u < ( sqrt ` 2 )
          )
          /\
          0 < v
        )
        ->
        8
        <_
        (
          ( ( u - v ) ^ 2 )
          +
          (
            (
              ( sqrt ` ( 2 - ( u ^ 2 ) ) )
              -
              ( 9 / v )
            )
            ^ 2
          )
        )
      )
    /\
    E. u e. RR E. v e. RR
      (
        (
          (
            0 < u
            /\
            u < ( sqrt ` 2 )
          )
          /\
          0 < v
        )
        /\
        (
          (
            ( ( u - v ) ^ 2 )
            +
            (
              (
                ( sqrt ` ( 2 - ( u ^ 2 ) ) )
                -
                ( 9 / v )
              )
              ^ 2
            )
          )
          =
          8
        )
      )
  ) $.
$}
