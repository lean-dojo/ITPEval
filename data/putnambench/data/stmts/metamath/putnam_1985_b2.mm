$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1985_b2: the recursively defined polynomial sequence with f_0 = 1,
  zero constant terms thereafter, and derivative
  f_(n+1)'(x) = (n+1) f_n(x+1) has f_100(1) = 101^99, its explicit prime
  factorization. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all NN0-indexed sequences of finite-support univariate real
  polynomials. The source polynomial equalities are written extensionally
  using eval1; this is equivalent because real polynomials are determined by
  their values. The expression using mPSDer is set.mm's formal derivative in
  the univariate polynomial ring over RRfld.

  The conclusion records that 101 is prime and that the value is 101^99.
  This is equivalent to the Lean prime-exponent function, the Isabelle
  prime-factor multiset with 99 copies of 101, and the Rocq product list.
  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F n x $.

  putnambench-putnam-1985-b2 $a |-
    A. F e. ( ( Base ` ( Poly1 ` RRfld ) ) ^m NN0 )
      (
        (
          A. x e. RR
            ( ( ( ( eval1 ` RRfld ) ` ( F ` 0 ) ) ` x ) = 1 )
          /\
          A. n e. NN
            ( ( ( ( eval1 ` RRfld ) ` ( F ` n ) ) ` 0 ) = 0 )
          /\
          A. n e. NN0 A. x e. RR
            (
              (
                (
                  ( eval1 ` RRfld )
                  `
                  (
                    ( ( ( 1o mPSDer RRfld ) ` (/) )
                      ` ( F ` ( n + 1 ) ) )
                  )
                )
                `
                x
              )
              =
              (
                ( n + 1 )
                x.
                ( ( ( eval1 ` RRfld ) ` ( F ` n ) ) ` ( x + 1 ) )
              )
            )
        )
        ->
        (
          ( ( ( 9 + 1 ) x. ( 9 + 1 ) ) + 1 ) e. Prime
          /\
          (
            (
              ( eval1 ` RRfld )
              `
              ( F ` ( ( 9 + 1 ) x. ( 9 + 1 ) ) )
            )
            `
            1
          )
            =
            (
              ( ( ( 9 + 1 ) x. ( 9 + 1 ) ) + 1 )
              ^
              ( ( ( 9 + 1 ) x. ( 9 + 1 ) ) - 1 )
            )
        )
      )
  $.
$}
