$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1978_b4: four integers can be chosen above every real bound while
  satisfying the specified symmetric quadratic-cubic Diophantine equation.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and RR are the integers and real numbers, respectively. The
  canonical inclusion of ZZ in RR makes each comparison r < a meaningful
  with exactly the coercion used in the source statements. Integer addition,
  multiplication, and squaring agree with the ambient complex-number
  operations displayed below, so the equation is unchanged.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c d r $.

  putnambench-putnam-1978-b4 $a |-
    A. r e. RR
      E. a e. ZZ E. b e. ZZ E. c e. ZZ E. d e. ZZ
        (
          (
            ( r < a /\ r < b )
            /\
            ( r < c /\ r < d )
          )
          /\
          (
            (
              (
                (
                  ( a ^ 2 )
                  +
                  ( b ^ 2 )
                )
                +
                ( c ^ 2 )
              )
              +
              ( d ^ 2 )
            )
            =
            (
              (
                (
                  (
                    ( a x. b )
                    x.
                    c
                  )
                  +
                  (
                    ( a x. b )
                    x.
                    d
                  )
                )
                +
                (
                  ( a x. c )
                  x.
                  d
                )
              )
              +
              (
                ( b x. c )
                x.
                d
              )
            )
          )
        )
  $.
$}
