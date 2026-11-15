$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2009_a2: the explicit local solution for the first component of a
  differentiable three-function real ODE system with specified initial
  values. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F, G, and H are arbitrary total real-valued functions.  The antecedent
  states their differentiability and the three differential equations on
  the open interval ( A , B ), together with the initial values at zero.
  The conclusion keeps the smaller interval endpoints C and D existential.

  The source's fractional real powers are rendered with set.mm's complex
  power operation ^c.  Around zero, the base
  sin(6x + pi/4) / cos(6x + pi/4)^2 is positive, so ^c agrees there with
  real power.  Since the conclusion is local and its interval may be
  shrunk, this gives a bidirectionally equivalent statement.
$)

${
  $d A B C D F G H x $.

  putnam2009a2 $a |- A. F e. ( RR ^m RR ) A. G e. ( RR ^m RR )
    A. H e. ( RR ^m RR ) A. A e. RR A. B e. RR
    (
      (
        ( A < 0 /\ 0 < B )
        /\
        (
          A. x e. ( A (,) B )
          (
            (
              (
                x e. dom ( RR _D F )
                /\
                x e. dom ( RR _D G )
              )
              /\
              x e. dom ( RR _D H )
            )
            /\
            (
              (
                ( ( RR _D F ) ` x )
                =
                (
                  (
                    ( ( 2 x. ( ( F ` x ) ^ 2 ) ) x. ( G ` x ) )
                    x. ( H ` x )
                  )
                  +
                  ( 1 / ( ( G ` x ) x. ( H ` x ) ) )
                )
                /\
                ( ( RR _D G ) ` x )
                =
                (
                  (
                    ( ( F ` x ) x. ( ( G ` x ) ^ 2 ) )
                    x. ( H ` x )
                  )
                  +
                  ( 4 / ( ( F ` x ) x. ( H ` x ) ) )
                )
              )
              /\
              ( ( RR _D H ) ` x )
              =
              (
                (
                  ( ( 3 x. ( F ` x ) ) x. ( G ` x ) )
                  x. ( ( H ` x ) ^ 2 )
                )
                +
                ( 1 / ( ( F ` x ) x. ( G ` x ) ) )
              )
            )
          )
          /\
          (
            (
              ( F ` 0 ) = 1
              /\
              ( G ` 0 ) = 1
            )
            /\
            ( H ` 0 ) = 1
          )
        )
      )
      ->
      E. C e. RR E. D e. RR
      (
        ( C < 0 /\ 0 < D )
        /\
        A. x e. ( C (,) D )
        (
          ( F ` x )
          =
          (
            ( 2 ^c ( ( -u 1 ) / ( 3 x. 4 ) ) )
            x.
            (
              (
                ( sin ` ( ( 6 x. x ) + ( _pi / 4 ) ) )
                /
                ( ( cos ` ( ( 6 x. x ) + ( _pi / 4 ) ) ) ^ 2 )
              )
              ^c
              ( 1 / 6 )
            )
          )
        )
      )
    ) $.
$}
