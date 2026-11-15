$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2008_a5: real polynomials whose values at 1 through n form a
  counterclockwise regular n-gon have at least one degree at least n minus
  one. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  Poly ` RR is set.mm's class of complex-valued polynomial functions with
  real coefficients. Evaluation at a natural number therefore agrees with
  evaluation of the source real polynomial followed by the canonical
  embedding into CC. Set.mm's deg is NN0-valued and assigns degree zero to
  the zero polynomial, matching the source natDegree convention.

  The internally existential O and nonzero z give the center and the complex
  radius-and-rotation factor. For every k from 1 through n, the displayed
  exponential gives the kth vertex in counterclockwise order. The final
  declaration is the single unproved $a corpus statement; this database
  contains no $p proof statement.
$)

${
  $d O f g k n z $.

  putnambench-putnam-2008-a5 $a |-
    A. n e. NN0
      A. f e. ( Poly ` RR )
        A. g e. ( Poly ` RR )
          (
            (
              3 <_ n
              /\
              E. O e. CC E. z e. CC
                (
                  z =/= 0
                  /\
                  A. k e. ( 1 ... n )
                    (
                      ( f ` k )
                      +
                      ( _i x. ( g ` k ) )
                    )
                    =
                    (
                      O
                      +
                      (
                        z
                        x.
                        (
                          exp
                          `
                          (
                            (
                              (
                                ( _i x. 2 )
                                x.
                                _pi
                              )
                              x.
                              k
                            )
                            /
                            n
                          )
                        )
                      )
                    )
                )
            )
            ->
            (
              ( n - 1 ) <_ ( deg ` f )
              \/
              ( n - 1 ) <_ ( deg ` g )
            )
          )
  $.
$}
