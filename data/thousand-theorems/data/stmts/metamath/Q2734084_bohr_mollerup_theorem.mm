$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2734084
  (thousand-theorems__metamath__Q2734084), "Bohr--Mollerup theorem": a positive
  real-valued function on the positive reals that is log-convex, satisfies
  f(x + 1) = x f(x), and is normalized by f(1) = 1 agrees there with the
  Gamma function. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR+ is the positive-real interval Ioi 0. The first premise below expands
  ConvexOn RR (Ioi 0) (log composed with F) using t in [0,1]; this is
  equivalent to the source's two nonnegative scalar weights summing to one,
  and RR+ is itself convex. SetMM's _G is its standard Gamma function.

  The recurrence, positivity, normalization, and equality conclusion retain
  the source quantifier scopes. The declaration below is the single unproved
  corpus $a statement; this file contains no $p proof statement.
$)

${
  $d F t x y $.

  thousand-theorems-q2734084-bohr-mollerup $a |-
    A. F e. ( RR ^m RR )
      (
        (
          (
            A. x e. RR+
              A. y e. RR+
                A. t e. ( 0 [,] 1 )
                  (
                    log
                    `
                    (
                      F
                      `
                      (
                        ( ( 1 - t ) x. x )
                        +
                        ( t x. y )
                      )
                    )
                  )
                  <_
                  (
                    (
                      ( 1 - t )
                      x.
                      ( log ` ( F ` x ) )
                    )
                    +
                    (
                      t
                      x.
                      ( log ` ( F ` y ) )
                    )
                  )
            /\
            A. y e. RR+
              ( F ` ( y + 1 ) )
              =
              ( y x. ( F ` y ) )
          )
          /\
          (
            A. y e. RR+
              0 < ( F ` y )
            /\
            ( F ` 1 ) = 1
          )
        )
        ->
        A. x e. RR+
          ( F ` x ) = ( _G ` x )
      )
  $.
$}
