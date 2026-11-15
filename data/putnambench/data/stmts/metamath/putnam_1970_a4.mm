$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1970_a4: a real sequence whose two-step differences tend to zero
  has its consecutive differences divided by the index tend to zero. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  The assertion quantifies over every real sequence indexed by NN0 and
  expands both limits into epsilon-threshold form. The shifted terms
  x(n+2)-x(n) and (x(n+1)-x(n))/(n+1) are exactly the Lean source and differ
  from the truncated-subtraction Isabelle and Rocq forms only in finitely
  many initial indices, so they define the same limits at infinity.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d e m n x $.

  putnambench-putnam-1970-a4 $a |- A. x e. ( RR ^m NN0 )
    (
      A. e e. RR
        (
          0 < e
          ->
          E. m e. NN0
            A. n e. NN0
              (
                m <_ n
                ->
                (
                  abs
                  `
                  (
                    ( x ` ( n + 2 ) )
                    -
                    ( x ` n )
                  )
                )
                < e
              )
        )
      ->
      A. e e. RR
        (
          0 < e
          ->
          E. m e. NN0
            A. n e. NN0
              (
                m <_ n
                ->
                (
                  abs
                  `
                  (
                    (
                      ( x ` ( n + 1 ) )
                      -
                      ( x ` n )
                    )
                    /
                    ( n + 1 )
                  )
                )
                < e
              )
        )
    )
  $.
$}
