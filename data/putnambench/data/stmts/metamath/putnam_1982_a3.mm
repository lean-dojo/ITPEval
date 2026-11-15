$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1982_a3: evaluation of an improper real integral involving
  arctangent as one half pi times the natural logarithm of pi. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The binder S. ( 0 (,) t ) F _d x is set.mm's real Lebesgue integral.
  For positive t, omitting the endpoints does not change the source interval
  integral. Values at nonpositive t are irrelevant to the limit at positive
  infinity.

  The relation ~~>r is set.mm's limit at positive infinity for a
  real-indexed function. The displayed limit is the explicit solution
  (pi / 2) * log(pi) given by the Rocq source and by the solution annotations
  in the Lean and Isabelle sources. The declaration is the single unproved
  $a corpus statement; this database contains no $p proof statement.
$)

${
  $d t x $.

  putnambench-putnam-1982-a3 $a |-
    (
      t e. RR |->
        S. ( 0 (,) t )
          (
            (
              ( arctan ` ( _pi x. x ) )
              -
              ( arctan ` x )
            )
            /
            x
          )
          _d x
    )
    ~~>r
    (
      ( _pi / 2 )
      x.
      ( log ` _pi )
    )
  $.
$}
