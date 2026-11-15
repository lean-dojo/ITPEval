$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2023_a2: the additional real solutions of p(1/x) = x^2 for a
  monic polynomial interpolating k^2 at the reciprocals of the nonzero
  integers from -n through n are exactly 1/(n!) and -1/(n!).
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  NN is set.mm's class of positive integers, and 2 || n is the source
  evenness condition. A in RR ^m NN0 is the complete coefficient function
  of an arbitrary real polynomial. Requiring coefficient 2n to be one and
  every later coefficient to vanish is exactly the condition that the
  polynomial is monic of degree 2n. Each displayed finite sum is its
  evaluation at the indicated real argument.

  The integer quantifier in the antecedent is equivalent to quantification
  over the source set S of real integers k with 1 <= |k| <= n. The class
  abstraction in the conclusion is the nonzero real solution set with S
  removed, and the right side is the explicit two-element solution set.
  Thus inlining S and the solution definition preserves the source
  proposition bidirectionally. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof
  declaration.
$)

${
  $d A i k n x $.

  putnambench-putnam-2023-a2 $a |-
    A. n e. NN
      A. A e. ( RR ^m NN0 )
        (
          (
            2 || n
            /\
            (
              ( A ` ( 2 x. n ) ) = 1
              /\
              A. i e. NN0
                (
                  ( 2 x. n ) < i
                  ->
                  ( A ` i ) = 0
                )
            )
            /\
            A. k e. ZZ
              (
                (
                  1 <_ ( abs ` k )
                  /\
                  ( abs ` k ) <_ n
                )
                ->
                (
                  sum_ i e. ( 0 ... ( 2 x. n ) )
                    (
                      ( A ` i )
                      x.
                      ( ( 1 / k ) ^ i )
                    )
                )
                =
                ( k ^ 2 )
              )
          )
          ->
          (
            {
              x e. RR |
              (
                (
                  x =/= 0
                  /\
                  (
                    sum_ i e. ( 0 ... ( 2 x. n ) )
                      (
                        ( A ` i )
                        x.
                        ( ( 1 / x ) ^ i )
                      )
                  )
                  =
                  ( x ^ 2 )
                )
                /\
                -.
                E. k e. ZZ
                  (
                    x = k
                    /\
                    (
                      1 <_ ( abs ` k )
                      /\
                      ( abs ` k ) <_ n
                    )
                  )
              )
            }
            =
            {
              ( 1 / ( ! ` n ) ) ,
              ( -u ( 1 / ( ! ` n ) ) )
            }
          )
        )
  $.
$}
