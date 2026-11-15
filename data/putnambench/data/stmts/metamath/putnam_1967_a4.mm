$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1967_a4: for a real parameter greater than one half, no integrable
  real-valued function satisfies the nonlinear interval-integral equation on
  the closed unit interval. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is set.mm's class of total real-valued functions on the reals.
  Membership of the restricted mapping in L^1 states integrability of u on
  [0,1]. For each x in [0,1], the Lebesgue integral is over the open interval
  (x,1); changing endpoint inclusion is immaterial for Lebesgue integration
  and matches the source interval integral. Each displayed convolution
  integrand is also required to belong to L^1 on its integration interval.

  The final declaration is the single unproved $a corpus statement. This
  database contains no $p proof statement.
$)

${
  $d L U x y $.

  putnambench-putnam-1967-a4 $a |- A. L e. RR
    (
      ( 1 / 2 ) < L
      ->
      -. E. U e. ( RR ^m RR )
        (
          ( y e. ( 0 [,] 1 ) |-> ( U ` y ) ) e. L^1
          /\
          (
            A. x e. ( 0 [,] 1 )
              (
                y e. ( x (,) 1 ) |->
                  (
                    ( U ` y )
                    x.
                    ( U ` ( y - x ) )
                  )
              ) e. L^1
            /\
            A. x e. ( 0 [,] 1 )
              ( U ` x )
              =
              (
                1
                +
                (
                  L
                  x.
                  S. ( x (,) 1 )
                    (
                      ( U ` y )
                      x.
                      ( U ` ( y - x ) )
                    )
                    _d y
                )
              )
          )
        )
    )
  $.
$}
