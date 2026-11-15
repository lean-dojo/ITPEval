$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1973_a3: for each positive integer n, the minimum of k + n/k
  over positive integers k has the same integer part as sqrt(4n + 1).
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The ordered infimum below is taken in the real numbers over exactly the
  values k + n/k with positive integer k. For positive integer n this
  nonempty set has an attained minimum, so the infimum is the b(n) used in
  the sources. Inlining b by this defining expression is equivalent to the
  external function-and-definition presentation in the Lean, Isabelle, and
  Rocq statements.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d k n x $.

  putnambench-putnam-1973-a3 $a |- A. n e. ZZ
    (
      0 < n
      ->
      (
        |_ `
          inf
            (
              {
                x e. RR |
                E. k e. ZZ
                  (
                    0 < k
                    /\
                    x = ( k + ( n / k ) )
                  )
              }
              ,
              RR
              ,
              <
            )
      )
      =
      (
        |_ `
          (
            sqrt
            `
            ( ( 4 x. n ) + 1 )
          )
      )
    )
  $.
$}
