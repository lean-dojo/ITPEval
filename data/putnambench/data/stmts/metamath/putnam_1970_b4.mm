$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_b4: a twice-differentiable real function with unit endpoint
  displacement, zero endpoint derivatives, and bounded first derivative
  has a point where the second derivative has absolute value at least 9/2.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of total real-valued functions. The first two
  entries of ( RR Dn F ) are the first and second real derivatives of F;
  requiring the closed unit interval to lie in their domains preserves the
  two differentiability assumptions. The remaining antecedents reproduce
  the endpoint and open-interval hypotheses, and the conclusion keeps the
  witness existentially quantified in the closed unit interval.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F t $.

  putnambench-putnam-1970-b4 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          (
            (
              ( 0 [,] 1 ) C_ dom ( ( RR Dn F ) ` 1 )
              /\
              ( 0 [,] 1 ) C_ dom ( ( RR Dn F ) ` 2 )
            )
            /\
            ( ( F ` 1 ) - ( F ` 0 ) ) = 1
          )
          /\
          (
            (
              ( ( ( RR Dn F ) ` 1 ) ` 0 ) = 0
              /\
              ( ( ( RR Dn F ) ` 1 ) ` 1 ) = 0
            )
            /\
            A. t e. ( 0 (,) 1 )
              (
                abs
                `
                ( ( ( RR Dn F ) ` 1 ) ` t )
              )
              <_
              ( 3 / 2 )
          )
        )
        ->
        E. t e. ( 0 [,] 1 )
          (
            ( 9 / 2 )
            <_
            (
              abs
              `
              ( ( ( RR Dn F ) ` 2 ) ` t )
            )
          )
      )
  $.
$}
