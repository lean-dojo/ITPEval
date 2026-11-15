$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1994_b2: a real line intersects the quartic
  x^4 + 9x^3 + cx^2 + 9x + 4 in four distinct real points exactly when
  c is less than 243/8. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The real parameters m and b describe the source line y = mx + b. The
  restricted class is exactly the set of real x-coordinates at which that
  line meets the graph of the quartic. Since the curve is a function of x,
  cardinality four is equivalent to four distinct intersection points.

  The right side expands the solution set identified in the Rocq source and
  in the Lean and Isabelle annotations. The final declaration is the single
  unproved $a corpus statement; this database contains no $p proof statement.
$)

${
  $d b c m x $.

  putnambench-putnam-1994-b2 $a |-
    A. c e. RR
      (
        (
          E. m e. RR E. b e. RR
            (
              #
              `
              {
                x e. RR
                |
                (
                  ( ( m x. x ) + b )
                  =
                  (
                    (
                      (
                        (
                          ( x ^ 4 )
                          +
                          ( 9 x. ( x ^ 3 ) )
                        )
                        +
                        ( c x. ( x ^ 2 ) )
                      )
                      +
                      ( 9 x. x )
                    )
                    +
                    4
                  )
                )
              }
            )
            =
            4
        )
        <->
        c < ( ( ; ; 2 4 3 ) / 8 )
      )
  $.
$}
