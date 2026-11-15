$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2001_a3: classification of the integer parameters for which
  x^4 - (2m + 4)x^2 + (m - 2)^2 factors into two nonconstant
  integer-coefficient polynomials. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Base ` ( Poly1 ` ZZring ) is SetMM's ring of all finite-support
  univariate polynomials over the integers, var1 is its indeterminate,
  algSc embeds integer constants, and coe1 is the complete
  nonnegative-integer-indexed coefficient function.

  A factor is nonconstant exactly when one of its coefficients at a
  positive index is nonzero. Thus the two existential coefficient
  conditions preserve the source degree-positive requirements without
  choosing an external degree bound.

  The pointwise biconditional over every integer m is equivalent to the
  source equality of the factorable-parameter set with the set of integer
  squares and twice integer squares. All factor and square witnesses remain
  internally existentially quantified. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d a b i j k m $.

  putnambench-putnam-2001-a3 $a |-
    A. m e. ZZ
      (
        E. a e. ( Base ` ( Poly1 ` ZZring ) )
          E. b e. ( Base ` ( Poly1 ` ZZring ) )
            (
              (
                (
                  (
                    4
                    ( .g ` ( mulGrp ` ( Poly1 ` ZZring ) ) )
                    ( var1 ` ZZring )
                  )
                  ( -g ` ( Poly1 ` ZZring ) )
                  (
                    ( ( algSc ` ( Poly1 ` ZZring ) ) ` ( ( 2 x. m ) + 4 ) )
                    ( .r ` ( Poly1 ` ZZring ) )
                    (
                      2
                      ( .g ` ( mulGrp ` ( Poly1 ` ZZring ) ) )
                      ( var1 ` ZZring )
                    )
                  )
                )
                ( +g ` ( Poly1 ` ZZring ) )
                ( ( algSc ` ( Poly1 ` ZZring ) ) ` ( ( m - 2 ) ^ 2 ) )
              )
              =
              (
                a
                ( .r ` ( Poly1 ` ZZring ) )
                b
              )
              /\
              (
                E. i e. NN ( ( coe1 ` a ) ` i ) =/= 0
                /\
                E. j e. NN ( ( coe1 ` b ) ` j ) =/= 0
              )
            )
        <->
        E. k e. ZZ
          (
            m = ( k ^ 2 )
            \/
            m = ( 2 x. ( k ^ 2 ) )
          )
      )
  $.
$}
