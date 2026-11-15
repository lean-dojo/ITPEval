$(
  Statement-only formalization of PutnamBench artifact putnam_1965_a6:
  a positive line ux + vy = 1 is tangent to the positive real-power curve
  x^m + y^m = 1 exactly when u and v satisfy the conjugate-exponent power
  equation. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The variables u, v, and m range over the reals. Real powers of positive
  bases are represented by set.mm's complex-power operation ^c, which equals
  exp(exponent * log(base)) and is real and positive on these domains.
  The positive tangency point x, y and the conjugate exponent n remain
  internally existentially quantified. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d m n u v x y $.

  putnambench-putnam-1965-a6 $a
    |- A. u e. RR A. v e. RR A. m e. RR
      (
        (
          (
            0 < u
            /\
            0 < v
          )
          /\
          1 < m
        )
        ->
        (
          E. x e. RR E. y e. RR
            (
              (
                0 < x
                /\
                0 < y
              )
              /\
              (
                ( ( u x. x ) + ( v x. y ) ) = 1
                /\
                (
                  ( ( x ^c m ) + ( y ^c m ) ) = 1
                  /\
                  (
                    u = ( x ^c ( m - 1 ) )
                    /\
                    v = ( y ^c ( m - 1 ) )
                  )
                )
              )
            )
          <->
          E. n e. RR
            (
              ( ( u ^c n ) + ( v ^c n ) ) = 1
              /\
              ( ( 1 / m ) + ( 1 / n ) ) = 1
            )
        )
      )
  $.
$}
