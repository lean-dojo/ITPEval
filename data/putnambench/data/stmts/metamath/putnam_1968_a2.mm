$(
  Statement-only formalization of PutnamBench artifact putnam_1968_a2:
  simultaneous nonzero rational approximation of two integer linear forms
  to prescribed integer targets within any positive real tolerance. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  The variables a through f range over the integers, t is the positive real
  tolerance, and r and s are the existentially quantified rational
  coefficients. Since ZZ is contained in QQ and QQ in RR in set.mm, the
  displayed arithmetic and comparisons use exactly the canonical inclusions
  appearing as coercions in the source statements.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c d e f r s t $.

  putnambench-putnam-1968-a2 $a |-
    A. a e. ZZ A. b e. ZZ A. c e. ZZ
      A. d e. ZZ A. e e. ZZ A. f e. ZZ
        A. t e. RR
          (
            (
              ( a x. d ) =/= ( b x. c )
              /\
              0 < t
            )
            ->
            E. r e. QQ E. s e. QQ
              (
                (
                  0
                  <
                  (
                    abs
                    `
                    ( ( ( r x. a ) + ( s x. b ) ) - e )
                  )
                  /\
                  (
                    abs
                    `
                    ( ( ( r x. a ) + ( s x. b ) ) - e )
                  )
                  <
                  t
                )
                /\
                (
                  0
                  <
                  (
                    abs
                    `
                    ( ( ( r x. c ) + ( s x. d ) ) - f )
                  )
                  /\
                  (
                    abs
                    `
                    ( ( ( r x. c ) + ( s x. d ) ) - f )
                  )
                  <
                  t
                )
              )
          )
  $.
$}
