$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1980_a3: evaluation of the real integral of
  1 / (1 + tan(x)^sqrt(2)) from zero to pi/2 as pi/4. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  The interval ( 0 (,) ( _pi / 2 ) ) is the open real interval used
  explicitly by the Lean and Rocq sources. It gives the same Lebesgue
  integral as the endpoint-inclusive interval in the Isabelle source.

  On this interval tan(x) is a positive real number. Therefore set.mm's
  complex-power operation ^c is real-valued here and equals
  exp(sqrt(2) * log(tan(x))), exactly the real-power encoding shared by the
  sources. The right side is the explicit solution from the Rocq source and
  the solution annotations in the Lean and Isabelle sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

putnambench-putnam-1980-a3 $a |- (
  S. ( 0 (,) ( _pi / 2 ) )
    (
      1
      /
      (
        1
        +
        (
          ( tan ` x )
          ^c
          ( sqrt ` 2 )
        )
      )
    )
    _d x
  =
  ( _pi / 4 )
) $.
