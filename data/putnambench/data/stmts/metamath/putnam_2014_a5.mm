$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2014_a5: the polynomials
  P_n(X) = 1 + 2 X + ... + n X^(n-1) are relatively prime for all
  distinct positive integers j and k. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P14A5Poly is set.mm's ring carrier of arbitrary finite-support
  complex-coefficient univariate polynomials. P14A5P maps each n in NN0 to
  the finite polynomial-ring sum from i = 1 through n of i times X^(i-1),
  exactly the polynomial family in the source.

  Coprimality is expressed by the equivalent Bezout identity in CC[X]:
  there are polynomials a and b such that a P_j + b P_k = 1. Both witnesses
  remain existentially quantified inside the conclusion. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof declaration.
$)

$c P14A5Poly P14A5P $.

p14a5-poly-syntax $a class P14A5Poly $.
p14a5-p-syntax $a class P14A5P $.

p14a5-poly-definition $a |- P14A5Poly =
  ( Base ` ( Poly1 ` CCfld ) ) $.

${
  $d i n $.

  p14a5-p-definition $a |- P14A5P =
    (
      n e. NN0 |->
        (
          ( Poly1 ` CCfld )
          gsum
          (
            i e. ( 1 ... n ) |->
              (
                ( ( algSc ` ( Poly1 ` CCfld ) ) ` i )
                ( .r ` ( Poly1 ` CCfld ) )
                (
                  ( i - 1 )
                  ( .g ` ( mulGrp ` ( Poly1 ` CCfld ) ) )
                  ( var1 ` CCfld )
                )
              )
          )
        )
    ) $.
$}

${
  $d a b j k $.

  putnambench-putnam-2014-a5 $a |-
    A. j e. NN
      A. k e. NN
        (
          j =/= k
          ->
          E. a e. P14A5Poly
            E. b e. P14A5Poly
              (
                (
                  a
                  ( .r ` ( Poly1 ` CCfld ) )
                  ( P14A5P ` j )
                )
                ( +g ` ( Poly1 ` CCfld ) )
                (
                  b
                  ( .r ` ( Poly1 ` CCfld ) )
                  ( P14A5P ` k )
                )
              )
              =
              ( 1r ` ( Poly1 ` CCfld ) )
        )
  $.
$}
