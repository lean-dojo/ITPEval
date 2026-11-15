$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_2000_b4: a continuous real function satisfying
  f(2x^2 - 1) = 2x f(x) for every real x vanishes on the closed interval
  from -1 to 1. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  F ranges over all total real-valued functions, and membership in
  ( RR -cn-> RR ) is set.mm's native assertion of global continuity.
  The functional equation retains its universal scope over RR, and the
  conclusion quantifies over the full real closed interval [ -1, 1 ].

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d F x $.

  putnambench-putnam-2000-b4 $a |-
    A. F e. ( RR ^m RR )
      (
        (
          F e. ( RR -cn-> RR )
          /\
          A. x e. RR
            (
              F ` ( ( 2 x. ( x ^ 2 ) ) - 1 )
            )
            =
            (
              ( 2 x. x )
              x.
              ( F ` x )
            )
        )
        ->
        A. x e. ( ( -u 1 ) [,] 1 )
          ( F ` x ) = 0
      )
  $.
$}
