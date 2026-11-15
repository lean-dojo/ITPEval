$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2022_b1: nonvanishing of every coefficient in the real power
  series of the exponential of an integer polynomial with zero constant
  coefficient and odd linear coefficient. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` ZZring ) is Set.mm's ring of arbitrary finite-support
  integer-coefficient univariate polynomials, and coe1 gives the complete
  coefficient function. Thus the unbounded coefficient sum evaluating P at
  a real x is actually finite and is exactly the real evaluation of P.

  RR ^m NN0 is the class of all real coefficient sequences. For each real
  x, the maps-to expression is the sequence of inclusive partial sums of
  sum_k b(k) x^k. Its convergence to exp(P(x)) is equivalent to the source
  HasSum hypothesis. Membership of coefficient one in Odd is precisely the
  odd-integer assumption, and the conclusion retains every nonnegative
  coefficient index.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof declaration.
$)

${
  $d P b k n x $.

  putnambench-putnam-2022-b1 $a |-
    A. P e. ( Base ` ( Poly1 ` ZZring ) )
      A. b e. ( RR ^m NN0 )
        (
          (
            (
              ( ( coe1 ` P ) ` 0 ) = 0
              /\
              ( ( coe1 ` P ) ` 1 ) e. Odd
            )
            /\
            A. x e. RR
              (
                n e. NN0 |->
                  sum_ k e. ( 0 ... n )
                    (
                      ( b ` k )
                      x.
                      ( x ^ k )
                    )
              )
              ~~>
              (
                exp
                `
                (
                  sum_ k e. NN0
                    (
                      ( ( coe1 ` P ) ` k )
                      x.
                      ( x ^ k )
                    )
                )
              )
          )
          ->
          A. k e. NN0
            ( b ` k ) =/= 0
        )
  $.
$}
