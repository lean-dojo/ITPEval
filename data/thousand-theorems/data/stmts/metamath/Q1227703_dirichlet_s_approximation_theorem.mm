$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1227703
  (thousand-theorems__metamath__Q1227703), "Dirichlet's approximation
  theorem": every point of a real additive circle has a positive multiple,
  bounded by a prescribed positive natural number, whose quotient norm is at
  most the circumference divided by one more than that bound. This root
  statement file contains no proof.
$)

$[ lib/set.mm $]

$(
  A point of AddCircle T is represented by an arbitrary real x, with two
  representatives identified when their difference is an integer multiple of
  the positive circumference T. For j in 1 ... n, the quotient norm of j times
  that point is at most T / (n + 1) exactly when some k in ZZ satisfies the
  absolute-value inequality below. Thus quantifying over all real x is
  equivalent to quantifying over every element of the quotient RR / T ZZ.

  The final declaration is the single unproved $a corpus statement; this root
  statement file contains no $p proof statement.
$)

${
  $d T j k n x $.

  thousand-theorems-q1227703-dirichlet-approximation-theorem $a |-
    A. T e. RR
      A. x e. RR
        A. n e. NN0
          (
            (
              0 < T
              /\
              0 < n
            )
            ->
            E. j e. ( 1 ... n )
              E. k e. ZZ
                (
                  abs `
                  (
                    ( j x. x )
                    -
                    ( k x. T )
                  )
                )
                <_
                (
                  T
                  /
                  ( n + 1 )
                )
          )
  $.
$}
