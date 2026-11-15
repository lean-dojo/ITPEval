$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_b3: a coprime factorization of an integer polynomial modulo a
  prime lifts to a factorization modulo every positive power of that prime.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  P86B3Poly is the class of all finite-support functions from NN0 to ZZ, a
  coefficient representation bidirectionally equivalent to arbitrary
  integer-coefficient polynomials. Polynomial multiplication is inlined as
  the finite convolution sum over 0 ... i.

  Divisibility of every coefficient difference is exactly the source
  congruence relation. The coefficient if ( i = 0 , 1 , 0 ) represents the
  constant polynomial one. Thus the two hypotheses are r*f + s*g congruent
  to 1 modulo p and f*g congruent to h modulo p, while the conclusion retains
  internally existential polynomials F and G and lifts only the product
  congruence to p^n.

  All declarations below are unproved $a statement encodings; this database
  contains no $p proof statement.
$)

$c P86B3Poly $.

p86b3-poly-syntax $a class P86B3Poly $.

${
  $d A i $.

  p86b3-poly-definition $a |- P86B3Poly =
    {
      A e. ( ZZ ^m NN0 ) |
        { i e. NN0 | ( A ` i ) =/= 0 } e. Fin
    }
  $.
$}

${
  $d F G f g h i k n p r s $.

  putnambench-putnam-1986-b3 $a |-
    A. n e. NN
      A. p e. Prime
        A. f e. P86B3Poly
          A. g e. P86B3Poly
            A. h e. P86B3Poly
              A. r e. P86B3Poly
                A. s e. P86B3Poly
                  (
                    (
                      A. i e. NN0
                        p
                        ||
                        (
                          (
                            (
                              sum_ k e. ( 0 ... i )
                                ( ( r ` k ) x. ( f ` ( i - k ) ) )
                            )
                            +
                            (
                              sum_ k e. ( 0 ... i )
                                ( ( s ` k ) x. ( g ` ( i - k ) ) )
                            )
                          )
                          -
                          if ( i = 0 , 1 , 0 )
                        )
                      /\
                      A. i e. NN0
                        p
                        ||
                        (
                          (
                            sum_ k e. ( 0 ... i )
                              ( ( f ` k ) x. ( g ` ( i - k ) ) )
                          )
                          -
                          ( h ` i )
                        )
                    )
                    ->
                    E. F e. P86B3Poly
                      E. G e. P86B3Poly
                        (
                          (
                            A. i e. NN0
                              p || ( ( F ` i ) - ( f ` i ) )
                            /\
                            A. i e. NN0
                              p || ( ( G ` i ) - ( g ` i ) )
                          )
                          /\
                          A. i e. NN0
                            ( p ^ n )
                            ||
                            (
                              (
                                sum_ k e. ( 0 ... i )
                                  ( ( F ` k ) x. ( G ` ( i - k ) ) )
                              )
                              -
                              ( h ` i )
                            )
                        )
                  )
  $.
$}
