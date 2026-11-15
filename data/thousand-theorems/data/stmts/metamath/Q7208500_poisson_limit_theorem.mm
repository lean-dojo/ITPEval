$(
  Statement-only formalization of Thousand Theorems corpus artifact Q7208500
  (thousand-theorems__metamath__Q7208500), "Poisson limit theorem": for each
  fixed nonnegative integer k, if the real sequence n * p(n) tends to r, then
  the kth binomial-probability term tends to exp(-r) * r^k / k!. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NN0 and RR are SetMM's nonnegative integers and real numbers. The relation
  ~~>t for the usual real topology is convergence of an NN0-indexed sequence,
  exactly the source's Tendsto along atTop.

  SetMM's infix subtraction is ordinary real subtraction, so the exponent is
  written conditionally to preserve Lean's natural-number truncated
  subtraction: it is n - k when k <= n and zero otherwise. The binomial
  coefficient n _C k, factorial ! ` k, real exponential, powers, products,
  and quotient therefore reproduce the source terms exactly.

  The following declaration is the single unproved corpus $a statement. This
  database contains no $p proof statement.
$)

${
  $d k n p r $.

  thousand-theorems-metamath-q7208500-poisson-limit-theorem $a |-
    A. p e. ( RR ^m NN0 )
      A. r e. RR
        A. k e. NN0
          (
            (
              n e. NN0 |->
                ( n x. ( p ` n ) )
            )
            ( ~~>t ` ( TopOpen ` RRfld ) )
            r
            ->
            (
              n e. NN0 |->
                (
                  (
                    ( n _C k )
                    x.
                    ( ( p ` n ) ^ k )
                  )
                  x.
                  (
                    ( 1 - ( p ` n ) )
                    ^
                    if ( k <_ n , ( n - k ) , 0 )
                  )
                )
            )
            ( ~~>t ` ( TopOpen ` RRfld ) )
            (
              (
                ( exp ` ( -u r ) )
                x.
                ( r ^ k )
              )
              /
              ( ! ` k )
            )
          )
  $.
$}
