$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2005_b5: a harmonic multivariate real polynomial divisible by the
  sum of the squares of its coordinate variables is identically zero. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  For n in NN, the ordinal n is the n-element variable-index set. Thus
  ( n mPoly RRfld ) is set.mm's ring of arbitrary finite-support
  multivariate polynomials over the real field, ( n mVar RRfld ) gives its
  coordinate polynomials, and ( n mPSDer RRfld ) gives formal partial
  differentiation.

  Each gsum is taken in the polynomial ring. The first hypothesis is exactly
  the vanishing sum of the second partial derivatives. The internally
  existential polynomial Q in the second hypothesis states that the sum of
  the coordinate squares divides P. The conclusion identifies P with the
  additive zero of the same polynomial ring.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d P Q i n $.

  putnambench-putnam-2005-b5 $a |-
    A. n e. NN
      A. P e. ( Base ` ( n mPoly RRfld ) )
        (
          (
            (
              ( n mPoly RRfld )
              gsum
              (
                i e. n |->
                  (
                    ( ( n mPSDer RRfld ) ` i )
                    `
                    (
                      ( ( n mPSDer RRfld ) ` i )
                      `
                      P
                    )
                  )
              )
            )
            =
            ( 0g ` ( n mPoly RRfld ) )
            /\
            E. Q e. ( Base ` ( n mPoly RRfld ) )
              (
                (
                  (
                    ( n mPoly RRfld )
                    gsum
                    (
                      i e. n |->
                        (
                          ( ( n mVar RRfld ) ` i )
                          ( .r ` ( n mPoly RRfld ) )
                          ( ( n mVar RRfld ) ` i )
                        )
                    )
                  )
                  ( .r ` ( n mPoly RRfld ) )
                  Q
                )
                =
                P
              )
          )
          ->
          P = ( 0g ` ( n mPoly RRfld ) )
        )
  $.
$}
