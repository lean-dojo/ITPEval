$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1986_a6: the value at one of a real polynomial constrained by a
  finite sparse-power identity is the product of its distinct positive
  exponents divided by n factorial. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m NN0 and NN0 ^m NN0 retain the source's arbitrary real-valued and
  natural-valued functions on all natural indices. The assumptions restrict
  positivity and pairwise distinctness of the exponent values only on the
  inclusive interval 1 ... n, exactly where the finite sum uses them.

  Base ` ( Poly1 ` RRfld ) is set.mm's ring of finite-support univariate
  real polynomials, and eval1 is polynomial evaluation. The conclusion
  inlines the explicit solution from the Rocq source and the solution
  annotations in the Isabelle and Lean sources. The final declaration is
  the single unproved $a corpus statement; this database contains no $p
  proof declaration.
$)

${
  $d a b f i j n x $.

  putnambench-putnam-1986-a6 $a |-
    A. n e. NN
      A. a e. ( RR ^m NN0 )
        A. b e. ( NN0 ^m NN0 )
          A. f e. ( Base ` ( Poly1 ` RRfld ) )
            (
              (
                (
                  A. i e. ( 1 ... n )
                    0 < ( b ` i )
                  /\
                  A. i e. ( 1 ... n )
                    A. j e. ( 1 ... n )
                      (
                        ( b ` i ) = ( b ` j )
                        ->
                        i = j
                      )
                )
                /\
                A. x e. RR
                  (
                    ( ( 1 - x ) ^ n )
                    x.
                    ( ( ( eval1 ` RRfld ) ` f ) ` x )
                  )
                  =
                  (
                    1
                    +
                    sum_ i e. ( 1 ... n )
                      (
                        ( a ` i )
                        x.
                        ( x ^ ( b ` i ) )
                      )
                  )
              )
              ->
              (
                ( ( ( eval1 ` RRfld ) ` f ) ` 1 )
                =
                (
                  (
                    prod_ i e. ( 1 ... n )
                      ( b ` i )
                  )
                  /
                  ( ! ` n )
                )
              )
            )
  $.
$}
