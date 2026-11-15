$(
  Statement-only formalization of PutnamBench corpus artifact
  putnam_1998_b2: the minimum perimeter of a triangle with one vertex at
  (a,b), one on the x-axis, and one on the line y = x is
  sqrt(2a^2 + 2b^2) when 0 < b < a. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  The set-builder contains exactly the perimeters obtained from real
  vertices (c,0) and (x,x). Its three strict inequalities are the source
  nondegeneracy conditions for the three side lengths. The ordered infimum
  is taken in RR; by the stated existence of a minimum, it is the source
  least perimeter. The right side inlines the solution value annotated in
  both ground-truth sources.

  The final declaration is the single unproved $a corpus statement; this
  database contains no $p proof statement.
$)

${
  $d a b c p x $.

  putnambench-putnam-1998-b2 $a |-
    A. a e. RR A. b e. RR
      (
        (
          0 < b
          /\
          b < a
        )
        ->
        (
          inf
          (
            {
              p e. RR |
              E. c e. RR E. x e. RR
                (
                  p
                  =
                  (
                    (
                      (
                        sqrt
                        `
                        (
                          ( ( a - c ) ^ 2 )
                          +
                          ( b ^ 2 )
                        )
                      )
                      +
                      (
                        sqrt
                        `
                        (
                          ( ( c - x ) ^ 2 )
                          +
                          ( x ^ 2 )
                        )
                      )
                    )
                    +
                    (
                      sqrt
                      `
                      (
                        ( ( a - x ) ^ 2 )
                        +
                        ( ( b - x ) ^ 2 )
                      )
                    )
                  )
                  /\
                  (
                    (
                      (
                        sqrt
                        `
                        (
                          ( ( a - c ) ^ 2 )
                          +
                          ( b ^ 2 )
                        )
                      )
                      +
                      (
                        sqrt
                        `
                        (
                          ( ( c - x ) ^ 2 )
                          +
                          ( x ^ 2 )
                        )
                      )
                    )
                    >
                    (
                      sqrt
                      `
                      (
                        ( ( a - x ) ^ 2 )
                        +
                        ( ( b - x ) ^ 2 )
                      )
                    )
                    /\
                    (
                      (
                        (
                          sqrt
                          `
                          (
                            ( ( a - c ) ^ 2 )
                            +
                            ( b ^ 2 )
                          )
                        )
                        +
                        (
                          sqrt
                          `
                          (
                            ( ( a - x ) ^ 2 )
                            +
                            ( ( b - x ) ^ 2 )
                          )
                        )
                      )
                      >
                      (
                        sqrt
                        `
                        (
                          ( ( c - x ) ^ 2 )
                          +
                          ( x ^ 2 )
                        )
                      )
                      /\
                      (
                        (
                          (
                            sqrt
                            `
                            (
                              ( ( c - x ) ^ 2 )
                              +
                              ( x ^ 2 )
                            )
                          )
                          +
                          (
                            sqrt
                            `
                            (
                              ( ( a - x ) ^ 2 )
                              +
                              ( ( b - x ) ^ 2 )
                            )
                          )
                        )
                        >
                        (
                          sqrt
                          `
                          (
                            ( ( a - c ) ^ 2 )
                            +
                            ( b ^ 2 )
                          )
                        )
                      )
                    )
                  )
                )
            }
            ,
            RR
            ,
            <
          )
          =
          (
            sqrt
            `
            (
              ( 2 x. ( a ^ 2 ) )
              +
              ( 2 x. ( b ^ 2 ) )
            )
          )
        )
      )
  $.
$}
