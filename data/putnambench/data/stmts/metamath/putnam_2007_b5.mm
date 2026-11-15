$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2007_b5: existence of k real polynomials expressing the kth power
  of floor(n/k) as a polynomial combination of its lower powers for every
  integer n. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` RRfld ) is set.mm's carrier of arbitrary finite-support
  univariate polynomials over the reals, and eval1 evaluates such a
  polynomial at a real input. For positive k, the interval 0 ... ( k - 1 )
  has exactly the k indices used in both source formulations.

  The function P is existentially quantified inside the quantifier over k,
  preserving that the polynomial family may depend on k. Quantifying k over
  NN is equivalent to the source natural-number domain together with k > 0,
  while n remains universally quantified over all integers. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d P i k n $.

  putnambench-putnam-2007-b5 $a |-
    A. k e. NN
      E. P e.
        (
          ( Base ` ( Poly1 ` RRfld ) )
          ^m
          ( 0 ... ( k - 1 ) )
        )
        A. n e. ZZ
          (
            ( ( |_ ` ( n / k ) ) ^ k )
            =
            (
              sum_ i e. ( 0 ... ( k - 1 ) )
                (
                  (
                    (
                      (
                        ( eval1 ` RRfld )
                        `
                        ( P ` i )
                      )
                      `
                      n
                    )
                    x.
                    ( ( |_ ` ( n / k ) ) ^ i )
                  )
                )
            )
          )
  $.
$}
