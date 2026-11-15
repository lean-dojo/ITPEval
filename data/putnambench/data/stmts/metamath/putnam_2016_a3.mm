$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2016_a3: evaluation of the unit-interval integral of a real
  function satisfying the given arctangent functional equation.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is set.mm's class of total real-valued functions on the reals.
  The antecedent states the source functional equation for every nonzero
  real x. The S. binder is set.mm's real Lebesgue integral over the closed
  unit interval, which agrees with the source interval integral.

  The right side is the explicit solution 3*pi/8 from the published problem
  and the Rocq source. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof declaration.
$)

${
  $d F x $.

  putnambench-putnam-2016-a3 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          A. x e. RR
            (
              x =/= 0
              ->
              (
                ( F ` x )
                +
                (
                  F
                  `
                  ( 1 - ( 1 / x ) )
                )
              )
              =
              ( arctan ` x )
            )
        )
        ->
        (
          S. ( 0 [,] 1 )
            ( F ` x )
            _d x
        )
        =
        ( ( 3 x. _pi ) / 8 )
      )
  $.
$}
