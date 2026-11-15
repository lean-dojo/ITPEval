$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1988_b6: infinitely many integer affine maps preserve
  triangular-number membership on all positive integers. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  The restricted class consists of all ordered integer pairs (a,b) such
  that, for every positive integer t, a*t+b is triangular exactly when t
  is triangular. A number is triangular precisely when it equals
  n*(n+1)/2 for an internally existential nonnegative integer n.

  Since n*(n+1) is even for every nonnegative integer n, set.mm's exact
  quotient by 2 agrees with the integer quotient in the ground-truth
  sources. Non-membership of the displayed set in Fin states that this
  full, unbounded set of integer pairs is infinite. The final declaration
  is the single unproved $a corpus statement; there is no $p proof
  statement in this database.
$)

${
  $d m n p t $.

  putnambench-putnam-1988-b6 $a |-
    -.
    {
      p e. ( ZZ X. ZZ ) |
      A. t e. ZZ
        (
          0 < t
          ->
          (
            E. n e. NN0
              (
                (
                  (
                    ( 1st ` p )
                    x.
                    t
                  )
                  +
                  ( 2nd ` p )
                )
                =
                (
                  (
                    n
                    x.
                    ( n + 1 )
                  )
                  /
                  2
                )
              )
            <->
            E. m e. NN0
              (
                t
                =
                (
                  (
                    m
                    x.
                    ( m + 1 )
                  )
                  /
                  2
                )
              )
          )
        )
    }
    e.
    Fin
  $.
$}
