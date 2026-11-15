$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_b5: a differentiable real function on (1,+infinity) satisfying
  the specified nonlinear differential equation tends to positive infinity.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of total real-valued functions; as in the formal
  sources, values at x <= 1 are an irrelevant total extension of the function
  whose hypotheses concern x > 1. The domain condition for RR _D F is exactly
  differentiability on that open ray, and the following equality is the given
  derivative equation there.

  The conclusion expands the atTop-to-atTop limit: every real lower target b
  is eventually a lower bound for F. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d F a b x $.

  putnambench-putnam-2009-b5 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          (
            { x e. RR | 1 < x }
            C_
            dom ( RR _D F )
          )
          /\
          A. x e. { x e. RR | 1 < x }
            (
              ( ( RR _D F ) ` x )
              =
              (
                (
                  ( x ^ 2 )
                  -
                  ( ( F ` x ) ^ 2 )
                )
                /
                (
                  ( x ^ 2 )
                  x.
                  ( ( ( F ` x ) ^ 2 ) + 1 )
                )
              )
            )
        )
        ->
        A. b e. RR
          E. a e. RR
            A. x e. RR
              (
                a <_ x
                ->
                b <_ ( F ` x )
              )
      )
  $.
$}
