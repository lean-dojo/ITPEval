$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1983_a6: evaluation as 2/9 of the positive-infinity limit of an
  exponentially scaled double integral over a right triangle. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The nested S. binders are set.mm's real Lebesgue integrals. For positive
  a, the open intervals omit only boundary points of the source triangle,
  which does not change the integral. Values at nonpositive a are irrelevant
  to the limit at positive infinity.

  The relation ~~>r is set.mm's limit at positive infinity for a
  real-indexed function. The value 2 / 9 is specified by the Rocq source and
  by the solution annotations in the Lean and Isabelle sources. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d a x y $.

  putnambench-putnam-1983-a6 $a |-
    (
      a e. RR |->
        (
          (
            ( a ^ 4 )
            /
            ( exp ` ( a ^ 3 ) )
          )
          x.
          S. ( 0 (,) a )
            (
              S. ( 0 (,) ( a - x ) )
                ( exp ` ( ( x ^ 3 ) + ( y ^ 3 ) ) )
                _d y
            )
            _d x
        )
    )
    ~~>r
    ( 2 / 9 )
  $.
$}
