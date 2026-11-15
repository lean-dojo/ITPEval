$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1995_a2: classification of the positive real parameter pairs for
  which the specified improper integral of nested square roots converges.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The S. binder is set.mm's real Lebesgue integral. Its closed interval
  matches the Lean Set.Icc integral and the Isabelle interval integral; the
  endpoint choices do not change the integral. The mapping indexed by the
  real upper endpoint t retains the source's finite lower endpoint b and
  exact nested-square-root integrand.

  The relation ~~>r is set.mm's finite real limit at positive infinity.
  Thus the existentially quantified L is exactly the internal convergence
  witness from the sources. The right side inlines the solution set
  {(a,b) in RR x RR | a = b}. The final declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d L a b t x $.

  putnambench-putnam-1995-a2 $a |-
    A. a e. RR A. b e. RR
      (
        ( 0 < a /\ 0 < b )
        ->
        (
          E. L e. RR
            (
              t e. RR |->
                S. ( b [,] t )
                  (
                    (
                      sqrt
                      `
                      (
                        ( sqrt ` ( x + a ) )
                        -
                        ( sqrt ` x )
                      )
                    )
                    -
                    (
                      sqrt
                      `
                      (
                        ( sqrt ` x )
                        -
                        ( sqrt ` ( x - b ) )
                      )
                    )
                  )
                  _d x
            )
            ~~>r
            L
          <->
          a = b
        )
      )
  $.
$}
