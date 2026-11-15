$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1976_a6: a bounded twice continuously differentiable real function
  satisfying the stated initial-value identity has a real point where the
  sum of the function and its second derivative is zero. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  RR ^m RR is the class of total real-valued functions. Membership in
  ( ( C^n ` RR ) ` 2 ) states global twice continuous differentiability,
  and the first two entries of ( RR Dn F ) are the first and second real
  derivatives. The function, its bounds, and the zero witness all retain
  their full real domains. The final declaration is the single unproved $a
  corpus statement; this database contains no $p proof statement.
$)

${
  $d F x y $.

  putnambench-putnam-1976-a6 $a |- A. F e. ( RR ^m RR )
    (
      (
        (
          F e. ( ( C^n ` RR ) ` 2 )
          /\
          A. x e. RR
            ( abs ` ( F ` x ) ) <_ 1
        )
        /\
        (
          ( ( F ` 0 ) ^ 2 )
          +
          ( ( ( ( RR Dn F ) ` 1 ) ` 0 ) ^ 2 )
        )
        =
        4
      )
      ->
      E. y e. RR
        (
          ( F ` y )
          +
          ( ( ( RR Dn F ) ` 2 ) ` y )
        )
        =
        0
    )
  $.
$}
