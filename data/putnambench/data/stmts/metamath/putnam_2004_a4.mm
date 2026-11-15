$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2004_a4: every finite product of real variables is identically a
  finite rational linear combination of nth powers of linear forms whose
  coefficients belong to -1, 0, or 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  For each positive integer n, N is a positive integer, c is a rational-valued
  function on 1 ... N, and a is a family indexed by 1 ... N of functions from
  1 ... n to { -1, 0, 1 }. The witnesses N, c, and a precede the universal
  quantifier over x, so the displayed equality is an identity in all n real
  variables, as required by the published problem.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d N a c i j n x $.

  putnambench-putnam-2004-a4 $a |-
    A. n e. NN
      E. N e. NN
        E. c e. ( QQ ^m ( 1 ... N ) )
          E. a e.
            ( ( { -u 1 , 0 , 1 } ^m ( 1 ... n ) ) ^m ( 1 ... N ) )
            A. x e. ( RR ^m ( 1 ... n ) )
              (
                prod_ j e. ( 1 ... n ) ( x ` j )
                =
                sum_ i e. ( 1 ... N )
                  (
                    ( c ` i )
                    x.
                    (
                      (
                        sum_ j e. ( 1 ... n )
                          ( ( ( a ` i ) ` j ) x. ( x ` j ) )
                      )
                      ^
                      n
                    )
                  )
              )
  $.
$}
