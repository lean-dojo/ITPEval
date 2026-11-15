$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2002_a1: the numerator polynomial in the nth derivative of
  1 / (x^k - 1), evaluated at one, equals (-k)^n times n factorial.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly1 ` RRfld is set.mm's ring of finite-support univariate real
  polynomials, and eval1 is its polynomial evaluation map. P ranges over
  all NN0-indexed families in this ring.

  P02A1Deriv totalizes set.mm's partial real derivative by assigning zero
  where the derivative does not exist. IterComp therefore agrees with the
  total iterated derivative operators in the source formalizations, including
  derivative order zero. Quantifying k over NN is equivalent to the source
  assumptions that k is a natural number and k > 0.

  Both divisions are explicitly zero at x^k = 1, matching the totalized field
  division used by the Lean and Rocq sources. The antecedent retains the
  derivative identity for every n in NN0 and every real x. The conclusion
  evaluates the same polynomial p(n) at one and gives the explicit Rocq value
  (-k)^n n!. The declarations below are unproved $a statement encodings; this
  database contains no $p proof statement.
$)

$c P02A1Deriv P02A1IterDeriv $.

p02a1-deriv-syntax $a class P02A1Deriv $.
p02a1-iter-deriv-syntax $a class ( P02A1IterDeriv n A ) $.

${
  $d A x $.

  p02a1-deriv-definition $a |- P02A1Deriv =
    (
      A e. ( RR ^m RR ) |->
        (
          x e. RR |->
            if (
              x e. dom ( RR _D A ) ,
              ( ( RR _D A ) ` x ) ,
              0
            )
        )
    ) $.
$}

p02a1-iter-deriv-definition $a |- ( P02A1IterDeriv n A ) =
  (
    ( ( IterComp ` P02A1Deriv ) ` n )
    `
    A
  ) $.

${
  $d A k n p x $.

  putnambench-putnam-2002-a1 $a |-
    A. k e. NN
    A. p e. ( ( Base ` ( Poly1 ` RRfld ) ) ^m NN0 )
      (
        (
          A. n e. NN0 A. x e. RR
            (
              (
                P02A1IterDeriv
                  n
                  (
                    x e. RR |->
                      if (
                        ( x ^ k ) = 1 ,
                        0 ,
                        (
                          1
                          /
                          (
                            ( x ^ k )
                            -
                            1
                          )
                        )
                      )
                  )
              )
              `
              x
            )
            =
            (
              if (
                ( x ^ k ) = 1 ,
                0 ,
                (
                  (
                    (
                      ( eval1 ` RRfld )
                      `
                      ( p ` n )
                    )
                    `
                    x
                  )
                  /
                  (
                    (
                      ( x ^ k )
                      -
                      1
                    )
                    ^
                    ( n + 1 )
                  )
                )
              )
            )
        )
        ->
        A. n e. NN0
          (
            (
              (
                ( eval1 ` RRfld )
                `
                ( p ` n )
              )
              `
              1
            )
            =
            (
              ( ( -u k ) ^ n )
              x.
              ( ! ` n )
            )
          )
      )
  $.
$}
