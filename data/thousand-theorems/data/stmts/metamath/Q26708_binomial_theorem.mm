$(
  Statement-only formalization of Thousand Theorems corpus artifact Q26708
  (thousand-theorems__metamath__Q26708), "Binomial theorem": in every
  commutative semiring, the nth power of a sum equals the finite sum of the
  corresponding products of powers weighted by binomial coefficients. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  CSRing is SetMM's class of arbitrary commutative unital semirings. Natural
  powers use the repeated operation of the multiplicative monoid, while
  ( n _C m ) ( .g ` R ) ( 1r ` R ) is the natural-number cast of the
  binomial coefficient into R. The inclusive interval 0 ... n is the same
  index set as Lean's range (n + 1), and R gsum uses the additive operation
  of R.

  The following declaration is the single unproved $a corpus statement. This
  root file itself contains no $p proof declaration; proofs verified during
  ITPEval come only from the imported lib/set.mm library.
$)

${
  $d R m n x y $.

  thousand-theorems-q26708-binomial-theorem $a |-
    A. R e. CSRing
      A. x e. ( Base ` R )
        A. y e. ( Base ` R )
          A. n e. NN0
            (
              (
                n
                ( .g ` ( mulGrp ` R ) )
                ( x ( +g ` R ) y )
              )
              =
              (
                R gsum
                  (
                    m e. ( 0 ... n ) |->
                      (
                        (
                          (
                            m
                            ( .g ` ( mulGrp ` R ) )
                            x
                          )
                          ( .r ` R )
                          (
                            ( n - m )
                            ( .g ` ( mulGrp ` R ) )
                            y
                          )
                        )
                        ( .r ` R )
                        (
                          ( n _C m )
                          ( .g ` R )
                          ( 1r ` R )
                        )
                      )
                  )
              )
            )
  $.
$}
