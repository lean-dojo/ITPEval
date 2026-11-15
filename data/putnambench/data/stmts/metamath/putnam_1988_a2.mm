$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_a2: for f(x) = exp(x^2), there exists an open real interval
  and a real function g, nonzero somewhere and differentiable on that
  interval, such that the incorrect product rule (fg)' = f'g' holds
  throughout the interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The source solution constant is defined or annotated as True, so its
  biconditional with the existence claim is logically equivalent to the
  existence claim asserted below. The witnesses a, b, and g remain internal.

  RR ^m RR is the class of all total real-valued functions. Membership of x
  in dom ( RR _D g ) expresses differentiability of g at x. The other two
  derivative functions are applied to the explicit maps y |-> exp(y^2) and
  y |-> exp(y^2) g(y), preserving the source derivative equality pointwise.
  The final declaration is a single unproved $a statement.
$)

${
  $d a b g x y $.

  putnambench-putnam-1988-a2 $a |- E. a e. RR E. b e. RR
    (
      a < b
      /\
      E. g e. ( RR ^m RR )
        (
          E. x e. ( a (,) b ) ( g ` x ) =/= 0
          /\
          A. x e. ( a (,) b )
            (
              x e. dom ( RR _D g )
              /\
              (
                (
                  RR
                  _D
                  (
                    y e. RR |->
                      (
                        ( exp ` ( y ^ 2 ) )
                        x.
                        ( g ` y )
                      )
                  )
                )
                ` x
              )
              =
              (
                (
                  (
                    RR
                    _D
                    ( y e. RR |-> ( exp ` ( y ^ 2 ) ) )
                  )
                  ` x
                )
                x.
                ( ( RR _D g ) ` x )
              )
            )
        )
    )
  $.
$}
