$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1999_a2: every real polynomial that is nonnegative on the real
  line is a finite nonempty sum of squares of real polynomials.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly ` RR is set.mm's class of complex-valued polynomial functions whose
  coefficients are real. Restriction to real inputs gives exactly the source
  real polynomials, with equality preserved because a real polynomial is
  determined by its values on the infinite set RR.

  The positive integer k and the map f internally encode a nonempty finite
  family indexed by 1 through k. This is equivalent to the finite-set form:
  a set can be enumerated, while repeated members of a finite family can be
  combined using real square roots of their positive multiplicities.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d f j k p x $.

  putnambench-putnam-1999-a2 $a |-
    A. p e. ( Poly ` RR )
      (
        A. x e. RR 0 <_ ( p ` x )
        ->
        E. k e. NN
          E. f e. ( ( Poly ` RR ) ^m ( 1 ... k ) )
            A. x e. RR
              ( p ` x )
              =
              sum_ j e. ( 1 ... k )
                ( ( ( f ` j ) ` x ) ^ 2 )
      )
  $.
$}
