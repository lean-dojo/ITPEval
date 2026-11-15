$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1989_b3: moment identities and normalized-moment convergence for a
  rapidly decaying real function satisfying a differential-functional
  equation on the nonnegative half-line. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  f is an arbitrary total real-valued function and g is its NN0-indexed real
  moment sequence. The first premise expresses differentiability
  relative to [0,+infinity); on its positive interior, the ordinary real
  derivative satisfies f'(x) = -3 f(x) + 6 f(2x). This relative formulation
  is the Isabelle statement and the problem text. It is equivalent for this
  theorem to Lean's global differentiability premise: a differentiable
  function on the half-line can be extended differentiably to the negative
  half-line without changing any hypothesis, moment, or conclusion here.

  The Lebesgue integral over (0,+infinity) defines every moment g(n). The
  first conclusion gives the resolved closed formula
  g(0)n!/(3^n product_(m=1)^n(1-2^(-m))). The two final clauses preserve
  existence of a real limit for g(n) 3^n / n! and the implication that
  convergence to zero forces g(0) = 0.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f g l m n x y $.

  putnambench-putnam-1989-b3 $a |-
    A. f e. ( RR ^m RR )
      A. g e. ( RR ^m NN0 )
        (
          (
            (
              A. x e. ( 0 [,) +oo )
                E. y e. RR
                  x
                  (
                    ( 0 [,) +oo )
                    _D
                    ( f |` ( 0 [,) +oo ) )
                  )
                  y
              /\
              A. x e. RR
                (
                  0 < x
                  ->
                  (
                    x e. dom ( RR _D f )
                    /\
                    ( ( RR _D f ) ` x )
                    =
                    (
                      ( ( -u 3 ) x. ( f ` x ) )
                      +
                      ( 6 x. ( f ` ( 2 x. x ) ) )
                    )
                  )
                )
            )
            /\
            (
              A. x e. RR
                (
                  0 <_ x
                  ->
                  ( abs ` ( f ` x ) )
                  <_
                  ( exp ` ( -u ( sqrt ` x ) ) )
                )
              /\
              A. n e. NN0
                ( g ` n )
                =
                S. ( 0 (,) +oo )
                  ( ( x ^ n ) x. ( f ` x ) )
                  _d x
            )
          )
          ->
          (
            (
              A. n e. NN0
                ( g ` n )
                =
                (
                  ( ( g ` 0 ) x. ( ! ` n ) )
                  /
                  (
                    ( 3 ^ n )
                    x.
                    prod_ m e. ( 1 ... n )
                      ( 1 - ( 2 ^ ( -u m ) ) )
                  )
                )
              /\
              E. l e. RR
                (
                  n e. NN0 |->
                    (
                      ( ( g ` n ) x. ( 3 ^ n ) )
                      /
                      ( ! ` n )
                    )
                )
                ~~>
                l
            )
            /\
            (
              (
                n e. NN0 |->
                  (
                    ( ( g ` n ) x. ( 3 ^ n ) )
                    /
                    ( ! ` n )
                  )
              )
              ~~>
              0
              ->
              ( g ` 0 ) = 0
            )
          )
        )
  $.
$}
